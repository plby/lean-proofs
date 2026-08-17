/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos54.FiniteSums

/-!
# Dyadic assembly for Erdős Problem 54

This file isolates the deterministic last step of the Conlon--Fox--Pham
argument.  Its only input is a family of finite, linearly sized dyadic blocks
whose every majority subset covers a long interval by distinct subset sums.
The strict inequality `2 * lowerConstant < upperConstant` makes consecutive
covered intervals overlap after discarding finitely many initial blocks.

The resulting union is positive, Ramsey `2`-complete, and has counting
function `O((log N)^2)`.  Thus the probabilistic part of the proof only has to
construct a value of `DyadicBlockSystem`.
-/

open scoped BigOperators

open Filter

namespace Erdos54

/-! ## The interface supplied by the robust-block theorem -/

/-- The properties required of the block at dyadic scale `k`.

The block lies in `[2^k,2^(k+1))`, has at most `d*k` elements, and every
subset containing at least half of it covers the indicated closed interval
by distinct subset sums. -/
def IsGoodDyadicBlock (a b d k : ℕ) (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)) ∧
    S.card ≤ d * k ∧
    ∀ T : Finset ℕ, T ⊆ S → S.card ≤ 2 * T.card →
      CoversInterval T (a * k * 2 ^ k) (b * k * 2 ^ k)

/-- A uniform family of robust dyadic blocks.  This is the exact deterministic
interface between the probabilistic block construction and the final
assembly. -/
structure DyadicBlockSystem where
  blocks : ℕ → Finset ℕ
  lowerConstant : ℕ
  upperConstant : ℕ
  sizeConstant : ℕ
  firstScale : ℕ
  lowerConstant_pos : 0 < lowerConstant
  constants_overlap : 2 * lowerConstant < upperConstant
  sizeConstant_pos : 0 < sizeConstant
  empty_before : ∀ k < firstScale, blocks k = ∅
  good : ∀ k ≥ firstScale,
    IsGoodDyadicBlock lowerConstant upperConstant sizeConstant k (blocks k)

/-- The raw existential conclusion naturally proved by the probabilistic
argument.  It does not require making simultaneous choices of all the finite
blocks. -/
def HasRobustDyadicBlocks : Prop :=
  ∃ a b d K : ℕ,
    0 < a ∧ 2 * a < b ∧ 0 < d ∧
      ∀ k ≥ K, ∃ S : Finset ℕ, IsGoodDyadicBlock a b d k S

/-- Choose one good block at every sufficiently large scale and normalize all
earlier blocks to the empty set.  This is the only use of choice in the
deterministic assembly. -/
theorem nonempty_dyadicBlockSystem_of_robustBlocks
    (h : HasRobustDyadicBlocks) : Nonempty DyadicBlockSystem := by
  classical
  obtain ⟨a, b, d, K, ha, hab, hd, hblocks⟩ := h
  let blocks : ℕ → Finset ℕ := fun k ↦
    if hk : K ≤ k then Classical.choose (hblocks k hk) else ∅
  refine ⟨
    { blocks := blocks
      lowerConstant := a
      upperConstant := b
      sizeConstant := d
      firstScale := K
      lowerConstant_pos := ha
      constants_overlap := hab
      sizeConstant_pos := hd
      empty_before := ?_
      good := ?_ }⟩
  · intro k hk
    simp [blocks, not_le_of_gt hk]
  · intro k hk
    simpa only [blocks, dif_pos hk] using Classical.choose_spec (hblocks k hk)

noncomputable def DyadicBlockSystem.ofRobustExistence
    (h : HasRobustDyadicBlocks) : DyadicBlockSystem :=
  Classical.choice (nonempty_dyadicBlockSystem_of_robustBlocks h)

/-- The set obtained by taking all blocks at or after `firstScale`. -/
def DyadicBlockSystem.carrier (D : DyadicBlockSystem) : Set ℕ :=
  {n | ∃ k, D.firstScale ≤ k ∧ n ∈ D.blocks k}

@[simp]
theorem DyadicBlockSystem.mem_carrier {D : DyadicBlockSystem} {n : ℕ} :
    n ∈ D.carrier ↔ ∃ k, D.firstScale ≤ k ∧ n ∈ D.blocks k :=
  Iff.rfl

theorem DyadicBlockSystem.block_subset_carrier (D : DyadicBlockSystem)
    {k : ℕ} (hk : D.firstScale ≤ k) : (D.blocks k : Set ℕ) ⊆ D.carrier := by
  intro n hn
  exact ⟨k, hk, hn⟩

theorem DyadicBlockSystem.positive (D : DyadicBlockSystem) :
    PositiveNatSet D.carrier := by
  rw [positiveNatSet_iff_zero_not_mem]
  rintro ⟨k, hk, hzero⟩
  have hbounds := (D.good k hk).1 0 hzero
  have : 0 < 2 ^ k := pow_pos (by omega) _
  omega

/-! ## A majority color and conversion to the public definition -/

/-- Every two-coloring of a finite set has a color occurring on at least half
of the set.  The multiplication formulation avoids division and rounding. -/
theorem exists_majority_fin_two {X : Type*} [DecidableEq X]
    (s : Finset X) (color : X → Fin 2) :
    ∃ c : Fin 2, s.card ≤ 2 * (s.filter fun x ↦ color x = c).card := by
  classical
  by_cases hzero : s.card ≤ 2 * (s.filter fun x ↦ color x = 0).card
  · exact ⟨0, hzero⟩
  · refine ⟨1, ?_⟩
    have hpartition :=
      Finset.card_filter_add_card_filter_not (s := s) (p := fun x ↦ color x = 0)
    have hfilters :
        (s.filter fun x ↦ ¬ color x = 0) =
          s.filter fun x ↦ color x = 1 := by
      ext x
      simp only [Finset.mem_filter]
      apply and_congr_right
      intro _
      have htwo (z : Fin 2) : z ≠ 0 ↔ z = 1 := by
        fin_cases z <;> simp
      exact htwo (color x)
    rw [hfilters] at hpartition
    omega

/-- A subset-sum witness made from natural numbers in `A` gives the witness
finset of the subtype `↑A` used by `MonochromaticSum`. -/
theorem monochromaticSum_of_subsetSumValues {A : Set ℕ} {T : Finset ℕ}
    {color : Coloring A 2} {c : Fin 2} {n : ℕ}
    (hTA : ∀ x ∈ T, x ∈ A)
    (hcolor : ∀ (x : ℕ) (hx : x ∈ T), color ⟨x, hTA x hx⟩ = c)
    (hn : n ∈ subsetSumValues T) : MonochromaticSum A 2 color n := by
  rw [mem_subsetSumValues] at hn
  obtain ⟨u, huT, hsum⟩ := hn
  let inclusion : ↑u ↪ ↑A :=
    ⟨fun x ↦ ⟨x.1, hTA x.1 (huT x.2)⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : ↑A ↦ (z : ℕ)) h)⟩
  let v : Finset ↑A := u.attach.map inclusion
  refine ⟨v, ?_, ?_⟩
  · refine ⟨c, ?_⟩
    intro y hy
    simp only [v, Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hcolor x.1 (huT x.2)
  · simp only [v, Finset.sum_map]
    calc
      (∑ x ∈ u.attach, ((inclusion x : ↑A) : ℕ)) =
          ∑ x ∈ u.attach, (x : ℕ) := by rfl
      _ = ∑ x ∈ u, x := Finset.sum_attach u (fun x ↦ x)
      _ = n := hsum

/-! ## Overlap of the covered intervals -/

/-- The strict constant gap implies that consecutive dyadic intervals
overlap once `k ≥ 2*a`. -/
theorem dyadic_interval_chain {a b k : ℕ} (_ha : 0 < a)
    (hab : 2 * a < b) (hk : 2 * a ≤ k) :
    a * (k + 1) * 2 ^ (k + 1) ≤ b * k * 2 ^ k + 1 := by
  have hcoeff : 2 * a * (k + 1) ≤ b * k := by
    nlinarith
  calc
    a * (k + 1) * 2 ^ (k + 1) = (2 * a * (k + 1)) * 2 ^ k := by ring
    _ ≤ (b * k) * 2 ^ k := Nat.mul_le_mul_right _ hcoeff
    _ ≤ b * k * 2 ^ k + 1 := by omega

theorem dyadic_interval_nonempty {a b k : ℕ} (ha : 0 < a)
    (hab : 2 * a < b) : a * k * 2 ^ k ≤ b * k * 2 ^ k := by
  have hab' : a ≤ b := by omega
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (k * 2 ^ k) hab'

/-- A chain of overlapping closed natural intervals, with unbounded right
endpoints, covers every integer from its first left endpoint onward. -/
theorem exists_mem_interval_of_chain (L U : ℕ → ℕ) (K : ℕ)
    (_hLU : ∀ k ≥ K, L k ≤ U k)
    (hchain : ∀ k ≥ K, L (k + 1) ≤ U k + 1)
    (hunbounded : ∀ n, ∃ k ≥ K, n ≤ U k) :
    ∀ n ≥ L K, ∃ k ≥ K, n ∈ Finset.Icc (L k) (U k) := by
  intro n hn
  have hex : ∃ m : ℕ, n ≤ U (K + m) := by
    obtain ⟨k, hk, hnk⟩ := hunbounded n
    exact ⟨k - K, by simpa [Nat.add_sub_of_le hk] using hnk⟩
  generalize hmdef : Nat.find hex = m
  have hm : n ≤ U (K + m) := by
    rw [← hmdef]
    exact Nat.find_spec hex
  refine ⟨K + m, by omega, Finset.mem_Icc.mpr ⟨?_, hm⟩⟩
  cases m with
  | zero => simpa using hn
  | succ m =>
      have hminimal : ¬ n ≤ U (K + m) := by
        exact Nat.find_min hex (by omega)
      have hover := hchain (K + m) (by omega)
      change L (K + (m + 1)) ≤ n
      have : U (K + m) + 1 ≤ n := by omega
      exact hover.trans this

/-! ## Ramsey completeness -/

/-- Every sufficiently late block supplies a monochromatic representation of
every number in its covered interval. -/
theorem DyadicBlockSystem.monochromatic_on_block (D : DyadicBlockSystem)
    (color : Coloring D.carrier 2) {k n : ℕ} (hk : D.firstScale ≤ k)
    (hn : n ∈ Finset.Icc
      (D.lowerConstant * k * 2 ^ k) (D.upperConstant * k * 2 ^ k)) :
    MonochromaticSum D.carrier 2 color n := by
  classical
  let blockColor : ℕ → Fin 2 := fun x ↦
    if hx : x ∈ D.blocks k then color ⟨x, D.block_subset_carrier hk hx⟩ else 0
  obtain ⟨c, hc⟩ := exists_majority_fin_two (D.blocks k) blockColor
  let T := (D.blocks k).filter fun x ↦ blockColor x = c
  have hTS : T ⊆ D.blocks k := Finset.filter_subset _ _
  have hcover : CoversInterval T
      (D.lowerConstant * k * 2 ^ k) (D.upperConstant * k * 2 ^ k) :=
    (D.good k hk).2.2 T hTS (by simpa [T] using hc)
  have hTA : ∀ x ∈ T, x ∈ D.carrier := by
    intro x hx
    exact D.block_subset_carrier hk (hTS hx)
  have hmono : ∀ (x : ℕ) (hx : x ∈ T), color ⟨x, hTA x hx⟩ = c := by
    intro x hx
    have hxT := Finset.mem_filter.mp hx
    simpa [blockColor, hxT.1] using hxT.2
  exact monochromaticSum_of_subsetSumValues hTA hmono (hcover hn)

/-- The union of a good dyadic block system is Ramsey `2`-complete. -/
theorem DyadicBlockSystem.ramseyTwoComplete (D : DyadicBlockSystem) :
    RamseyTwoComplete D.carrier := by
  intro color
  let K₀ := max D.firstScale (2 * D.lowerConstant)
  have hKfirst : D.firstScale ≤ K₀ := le_max_left _ _
  have hKa : 2 * D.lowerConstant ≤ K₀ := le_max_right _ _
  let L : ℕ → ℕ := fun k ↦ D.lowerConstant * k * 2 ^ k
  let U : ℕ → ℕ := fun k ↦ D.upperConstant * k * 2 ^ k
  have hLU : ∀ k ≥ K₀, L k ≤ U k := by
    intro k hk
    exact dyadic_interval_nonempty D.lowerConstant_pos D.constants_overlap
  have hchain : ∀ k ≥ K₀, L (k + 1) ≤ U k + 1 := by
    intro k hk
    exact dyadic_interval_chain D.lowerConstant_pos D.constants_overlap
      (hKa.trans hk)
  have hunbounded : ∀ n, ∃ k ≥ K₀, n ≤ U k := by
    intro n
    refine ⟨max K₀ n, le_max_left _ _, ?_⟩
    have hnle : n ≤ max K₀ n := le_max_right _ _
    have hbpos : 0 < D.upperConstant := by
      have := D.constants_overlap
      omega
    have hpowpos : 0 < 2 ^ max K₀ n := pow_pos (by norm_num) _
    have hpow : 1 ≤ 2 ^ max K₀ n := hpowpos
    change n ≤ D.upperConstant * max K₀ n * 2 ^ max K₀ n
    calc
      n ≤ max K₀ n := hnle
      _ ≤ D.upperConstant * max K₀ n := by
        calc
          max K₀ n = 1 * max K₀ n := by simp
          _ ≤ D.upperConstant * max K₀ n :=
            Nat.mul_le_mul_right _ hbpos
      _ ≤ D.upperConstant * max K₀ n * 2 ^ max K₀ n := by
        simpa only [Nat.mul_assoc, Nat.mul_one] using
          Nat.mul_le_mul_left (D.upperConstant * max K₀ n) hpow
  refine ⟨L K₀, ?_⟩
  intro n hn
  obtain ⟨k, hk, hnk⟩ :=
    exists_mem_interval_of_chain L U K₀ hLU hchain hunbounded n hn
  apply D.monochromatic_on_block color (hKfirst.trans hk)
  simpa [L, U] using hnk

/-! ## The quadratic logarithmic counting bound -/

/-- A prefix of the dyadic union is contained in the union of blocks whose
scale is at most `Nat.log 2 N`. -/
theorem DyadicBlockSystem.prefix_subset_blocks (D : DyadicBlockSystem)
    {N n : ℕ} (hnN : n ∈ Finset.Icc 1 N) (hnA : n ∈ D.carrier) :
    n ∈ (Finset.range (Nat.log 2 N + 1)).biUnion D.blocks := by
  obtain ⟨k, hkfirst, hnk⟩ := hnA
  have hkpow : 2 ^ k ≤ n := (D.good k hkfirst).1 n hnk |>.1
  have hklog : k ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (hkpow.trans (Finset.mem_Icc.mp hnN).2)
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hnk⟩

/-- Natural-number form of the quadratic bound.  It is convenient on its own
and makes the later real asymptotic argument completely transparent. -/
theorem DyadicBlockSystem.countUpTo_le_log_sq (D : DyadicBlockSystem)
    (N : ℕ) :
    countUpTo D.carrier N ≤
      D.sizeConstant * (Nat.log 2 N + 1) ^ 2 := by
  classical
  let m := Nat.log 2 N
  have hprefix :
      (Finset.Icc 1 N).filter (fun n ↦ n ∈ D.carrier) ⊆
        (Finset.range (m + 1)).biUnion D.blocks := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    simpa [m] using D.prefix_subset_blocks hn'.1 hn'.2
  have hcard : countUpTo D.carrier N ≤
      ((Finset.range (m + 1)).biUnion D.blocks).card := by
    simpa [countUpTo] using Finset.card_le_card hprefix
  have hunion : ((Finset.range (m + 1)).biUnion D.blocks).card ≤
      ∑ k ∈ Finset.range (m + 1), (D.blocks k).card :=
    Finset.card_biUnion_le
  have hsum : (∑ k ∈ Finset.range (m + 1), (D.blocks k).card) ≤
      ∑ k ∈ Finset.range (m + 1), D.sizeConstant * k := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkfirst : D.firstScale ≤ k
    · exact (D.good k hkfirst).2.1
    · rw [D.empty_before k (by omega)]
      simp
  have hlinear : (∑ k ∈ Finset.range (m + 1), D.sizeConstant * k) ≤
      ∑ _k ∈ Finset.range (m + 1), D.sizeConstant * m := by
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := by simpa using Finset.mem_range.mp hk
    exact Nat.mul_le_mul_left _ hkm
  have hfinal : (∑ _k ∈ Finset.range (m + 1), D.sizeConstant * m) ≤
      D.sizeConstant * (m + 1) ^ 2 := by
    have heq : (∑ _k ∈ Finset.range (m + 1), D.sizeConstant * m) =
        (m + 1) * (D.sizeConstant * m) := by simp
    rw [heq]
    nlinarith
  exact hcard.trans (hunion.trans (hsum.trans (hlinear.trans (by simpa [m] using hfinal))))

/-- The dyadic union has an `O((log N)^2)` counting function. -/
theorem DyadicBlockSystem.hasLogSquaredCountingBound (D : DyadicBlockSystem) :
    HasLogSquaredCountingBound D.carrier := by
  let C : ℝ := (D.sizeConstant : ℝ) * (2 / Real.log 2) ^ 2
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    have hdpos : 0 < (D.sizeConstant : ℝ) := by exact_mod_cast D.sizeConstant_pos
    exact mul_pos hdpos (sq_pos_of_pos (div_pos (by norm_num) hlogtwo))
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hnat := D.countUpTo_le_log_sq N
  have hnatReal : (countUpTo D.carrier N : ℝ) ≤
      (D.sizeConstant : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hnat
  have hlog : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb N 2
  have hratio : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlogtwo]
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa only [one_mul] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNreal
  have hmplus : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      2 * (Real.log (N : ℝ) / Real.log 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith
  have hsquare : (((Nat.log 2 N + 1 : ℕ) : ℝ)) ^ 2 ≤
      (2 * (Real.log (N : ℝ) / Real.log 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmplus 2
  calc
    (countUpTo D.carrier N : ℝ) ≤
        (D.sizeConstant : ℝ) * (((Nat.log 2 N + 1 : ℕ) : ℝ)) ^ 2 := hnatReal
    _ ≤ (D.sizeConstant : ℝ) *
        (2 * (Real.log (N : ℝ) / Real.log 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = C * (Real.log (N : ℝ)) ^ 2 := by
      dsimp [C]
      ring

/-! ## The complete deterministic implication -/

/-- Any proved robust dyadic block system yields the exact upper-bound
resolution asserted by Conlon, Fox, and Pham. -/
theorem upperBound_of_goodDyadicBlocks (D : DyadicBlockSystem) :
    ConlonFoxPhamUpperBoundTwo := by
  exact ⟨D.carrier, D.positive, D.ramseyTwoComplete,
    D.hasLogSquaredCountingBound⟩

/-- Existential packaging convenient for the terminal main theorem: the
probabilistic development proves `Nonempty DyadicBlockSystem`, and no
assumption remains after that theorem is supplied. -/
theorem upperBound_of_robust_blocks (h : Nonempty DyadicBlockSystem) :
    ConlonFoxPhamUpperBoundTwo :=
  upperBound_of_goodDyadicBlocks (Classical.choice h)

/-- Raw existential form used when the robust-block theorem is stated exactly
as it arises from the finite probabilistic argument. -/
theorem upperBound_of_robust_block_existence (h : HasRobustDyadicBlocks) :
    ConlonFoxPhamUpperBoundTwo :=
  upperBound_of_goodDyadicBlocks (DyadicBlockSystem.ofRobustExistence h)

end Erdos54
