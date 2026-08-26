/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Initial

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Stage arithmetic packages for Erdős Problem 330

The concrete service step has many interval inequalities.  This file collects
the reusable arithmetic consequences of the standard choice `N = X + 1` and
large service/tail lengths.
-/

namespace Erdos330

open scoped Pointwise

namespace StageParams

/-- The non-density, non-helper arithmetic hypotheses required by a service step. -/
structure CoreInequalities {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) : Prop where
  hN : st.X < params.N
  hK : st.X < params.K
  hX_next : st.X ≤ params.nextX
  hR_next : st.R ≤ params.nextR
  hlower_height : params.N + params.L ≤ params.nextX
  hprivate_height : params.serviceR ≤ params.nextX
  hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX
  hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR
  hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX
  hCL : 3 * st.M ≤ params.L
  hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1
  hlower_end :
    2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1
  hML : params.Mplus ≤ params.L
  hCLZ : 3 * st.M ≤ params.LZ
  htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1
  htail_end :
    2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1
  hMLZ : params.Mplus ≤ params.LZ

theorem coreInequalities_of_standardN_large {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hN_eq : params.N = st.X + 1)
    (hL_service : params.Mplus + 3 * st.M ≤ params.L)
    (hR_service : st.R ≤ params.serviceR)
    (hLZ_private : st.X ≤ params.LZ)
    (hLZ_headroom : 4 * params.Mplus ≤ params.LZ)
    (hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ) :
    params.CoreInequalities := by
  have hML : params.Mplus ≤ params.L := by omega
  have hCL : 3 * st.M ≤ params.L := by omega
  have hMLZ : params.Mplus ≤ params.LZ := by omega
  have hCLZ : 3 * st.M ≤ params.LZ := by omega
  have hOldReservoir : st.H + 3 * st.M ≤ st.X := st.reservoir_long
  have hOldHeadroom : st.H + st.X + 3 * st.M ≤ st.R := st.headroom
  have htailEnd :
      2 * params.K + params.Mplus + 3 * st.M ≤
        st.X + params.K + params.LZ + 1 := by
    simp only [hN_eq, serviceR, protectedEndpoint, K]
    omega
  have hHeadroom :
      params.K + params.nextX + 3 * params.Mplus ≤ params.nextR := by
    rw [nextR]
    apply Nat.le_sub_of_add_le
    rw [nextX]
    omega
  have hService_ge_X : st.X ≤ params.serviceR := by
    simp only [hN_eq, serviceR]
    omega
  have hService_le_KLZ : params.serviceR ≤ params.K + params.LZ := by
    rw [K, protectedEndpoint]
    calc
      params.serviceR = params.serviceR - st.X + st.X :=
        (Nat.sub_add_cancel hService_ge_X).symm
      _ ≤ params.serviceR - st.X + params.LZ := by omega
      _ ≤ params.serviceR - st.X + 1 + params.LZ := by omega
  have hPrivateHeight : params.serviceR ≤ params.nextX := by
    rw [nextX]
    exact hService_le_KLZ
  have hRNext : st.R ≤ params.nextR := by
    have hnextX_le_nextR : params.nextX ≤ params.nextR := by omega
    exact le_trans hR_service (le_trans hPrivateHeight hnextX_le_nextR)
  refine {
    hN := ?_
    hK := ?_
    hX_next := ?_
    hR_next := hRNext
    hlower_height := ?_
    hprivate_height := hPrivateHeight
    hreservoir_long := ?_
    hheadroom := hHeadroom
    hendpoint_le_nextX := ?_
    hCL := hCL
    hlower_start := ?_
    hlower_end := ?_
    hML := hML
    hCLZ := hCLZ
    htail_start := ?_
    htail_end := htailEnd
    hMLZ := hMLZ
  } <;>
    simp only [hN_eq, serviceR, protectedEndpoint, K, nextX] <;>
    omega

/--
For any fixed CRT gadget data, the purely numeric part of a service step can
be made valid by taking explicit sufficiently large lengths.
-/
theorem exists_params_with_coreInequalities {st : StageState} {a b p : ℕ}
    (Dplus : Finset (ZMod (activatedM st b p)))
    (G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedM st b p) a Dplus) :
    ∃ params : StageParams st a b p,
      params.Dplus = Dplus ∧ params.N = st.X + 1 ∧ params.CoreInequalities := by
  let Mnew := activatedM st b p
  let L := st.R + Mnew + 3 * st.M
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params : StageParams st a b p := {
    Dplus := Dplus
    G := G
    N := st.X + 1
    L := L
    LZ := LZ
  }
  refine ⟨params, rfl, rfl, ?_⟩
  refine coreInequalities_of_standardN_large params rfl ?_ ?_ ?_ ?_ ?_
  · dsimp [params, L, Mplus, Mnew]
    omega
  · dsimp [params, L, serviceR, Mplus, Mnew]
    apply Nat.le_sub_of_add_le
    omega
  · dsimp [params, LZ]
    omega
  · dsimp [params, LZ, Mplus, Mnew]
    omega
  · dsimp [params, LZ, L]
    omega

theorem exists_params_with_coreInequalities_and_densityGap {st : StageState} {a b p : ℕ}
    (Dplus : Finset (ZMod (activatedM st b p)))
    (G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedM st b p) a Dplus) :
    ∃ params : StageParams st a b p,
      params.Dplus = Dplus ∧ params.N = st.X + 1 ∧ params.CoreInequalities ∧
        st.X + params.N + params.L + params.Mplus + 1 < params.protectedEndpoint := by
  let Mnew := activatedM st b p
  let L := st.X + 2 * Mnew + st.R + 3 * st.M + 1
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params : StageParams st a b p := {
    Dplus := Dplus
    G := G
    N := st.X + 1
    L := L
    LZ := LZ
  }
  refine ⟨params, rfl, rfl, ?_, ?_⟩
  · refine coreInequalities_of_standardN_large params rfl ?_ ?_ ?_ ?_ ?_
    · dsimp [params, L, Mplus, Mnew]
      omega
    · dsimp [params, L, serviceR, Mplus, Mnew]
      apply Nat.le_sub_of_add_le
      omega
    · dsimp [params, LZ]
      omega
    · dsimp [params, LZ, Mplus, Mnew]
      omega
    · dsimp [params, LZ, L]
      omega
  · dsimp [params, L, protectedEndpoint, serviceR, Mplus, Mnew]
    omega

end StageParams

theorem zmodFinset_nonempty_of_add_self_eq_univ {M : ℕ} {D : Finset (ZMod M)}
    (hD_add : ((D : Set (ZMod M)) + (D : Set (ZMod M))) = Set.univ) :
    ∃ ρ : ZMod M, ρ ∈ D := by
  have hzero : (0 : ZMod M) ∈ ((D : Set (ZMod M)) + (D : Set (ZMod M))) := by
    rw [hD_add]
    exact Set.mem_univ _
  rcases hzero with ⟨ρ, hρ, _θ, _hθ, _hsum⟩
  exact ⟨ρ, hρ⟩

theorem nat_le_eight_mul_of_floor_density {M C card len endpoint : ℕ}
    (hMpos : 0 < M) (hMle : M ≤ 2 * C * card)
    (hlen : endpoint + 4 * M ≤ 4 * len) :
    endpoint ≤ 8 * C * (card * (len / M)) := by
  let q := len / M
  have hlen_lt : len < M * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ len hMpos
  have hlen_lt' : len < M * q + M := by
    simpa [Nat.mul_succ] using hlen_lt
  have h4len_lt : 4 * len < 4 * (M * q + M) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mpr hlen_lt'
  have hendpoint_le : endpoint ≤ 4 * M * q := by
    nlinarith
  have hmain : 4 * M * q ≤ 8 * C * (card * q) := by
    nlinarith
  exact hendpoint_le.trans hmain

theorem exists_nat_reciprocal_budget_bound {x : ℝ} (hx : x < (1 / 2 : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ x + (1 : ℝ) / N ≤ (1 / 2 : ℝ) := by
  have hε : 0 < (1 / 2 : ℝ) - x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hn' : (1 : ℝ) / (n + 1 : ℕ) < (1 / 2 : ℝ) - x := by
    simpa [Nat.cast_add, Nat.cast_one] using hn
  linarith

theorem exists_nat_reciprocal_budget_strict {x : ℝ} (hx : x < (1 / 2 : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ x + (1 : ℝ) / N < (1 / 2 : ℝ) := by
  have hε : 0 < (1 / 2 : ℝ) - x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hn' : (1 : ℝ) / (n + 1 : ℕ) < (1 / 2 : ℝ) - x := by
    simpa [Nat.cast_add, Nat.cast_one] using hn
  linarith

def StageState.HasStrictReciprocalBudget (st : StageState) : Prop :=
  st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) < (1 / 2 : ℝ)

theorem StageParams.exists_dormant_from_tail_of_Dplus_add_self
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hbS : b ∈ st.S) (hK : st.X < params.K) (hMLZ : params.Mplus ≤ params.LZ)
    (hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ) :
    ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b := by
  let : NeZero params.Mplus := by
    dsimp [StageParams.Mplus]
    infer_instance
  obtain ⟨ρ, hρ⟩ := zmodFinset_nonempty_of_add_self_eq_univ hDplus_add
  obtain ⟨c, hcK, hcKM, hcρ⟩ := exists_natCast_eq_zmod_in_Icc_len params.Mplus params.K ρ
  have hcTail : c ∈ params.tailBlock := by
    rw [StageParams.mem_tailBlock]
    refine ⟨hcK, ?_, ?_⟩
    · rw [StageParams.nextX]
      omega
    · simpa [StageParams.Mplus, hcρ] using hρ
  refine ⟨c, params.tailBlock_subset_nextS hcTail, ?_⟩
  intro hcActive
  have hXc : st.X < c := hK.trans_le hcK
  rw [activatedActiveSet] at hcActive
  rcases Finset.mem_insert.mp hcActive with hcEq | hcP
  · have hbX : b ≤ st.X := st.S_le_X b hbS
    omega
  · exact (not_lt_of_ge (st.active_le_X hcP)) hXc

theorem StageParams.protectedSubblock_density_arithmetic
    {st : StageState} {a b p lo hi : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hPstar_pos : 0 < params.G.Pstar.card)
    (hMle : params.Mplus ≤ hi - lo) :
    1 * params.protectedEndpoint ≤
      (params.protectedEndpoint + 1) *
        (params.G.Pstar.card * ((hi - lo) / params.Mplus)) := by
  let : NeZero params.Mplus := by
    dsimp [StageParams.Mplus]
    infer_instance
  have hMpos : 0 < params.Mplus := NeZero.pos params.Mplus
  have hdiv_pos : 0 < (hi - lo) / params.Mplus := Nat.div_pos hMle hMpos
  have hfactor :
      1 ≤ params.G.Pstar.card * ((hi - lo) / params.Mplus) := by
    have hP : 1 ≤ params.G.Pstar.card := Nat.succ_le_of_lt hPstar_pos
    have hD : 1 ≤ (hi - lo) / params.Mplus := Nat.succ_le_of_lt hdiv_pos
    simpa using Nat.mul_le_mul hP hD
  have hmul :
      params.protectedEndpoint + 1 ≤
        (params.protectedEndpoint + 1) *
          (params.G.Pstar.card * ((hi - lo) / params.Mplus)) := by
    simpa using Nat.mul_le_mul_left (params.protectedEndpoint + 1) hfactor
  omega

theorem StageParams.protectedSubblock_fixedDensity_arithmetic
    {st : StageState} {a b p lo hi C : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hMle : params.Mplus ≤ 2 * C * params.G.Pstar.card)
    (hlen : params.protectedEndpoint + 4 * params.Mplus ≤ 4 * (hi - lo)) :
    1 * params.protectedEndpoint ≤
      (8 * C) * (params.G.Pstar.card * ((hi - lo) / params.Mplus)) := by
  let : NeZero params.Mplus := by
    dsimp [StageParams.Mplus]
    infer_instance
  simpa using
    nat_le_eight_mul_of_floor_density (M := params.Mplus) (C := C)
      (card := params.G.Pstar.card) (len := hi - lo)
      (endpoint := params.protectedEndpoint) (NeZero.pos params.Mplus) hMle hlen

theorem StageParams.tailBlock_fixedDensity_arithmetic
    {st : StageState} {a b p C : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hMle : params.Mplus ≤ 2 * C * params.Dplus.card)
    (hlen : params.nextX + 1 + 4 * params.Mplus ≤ 4 * params.LZ) :
    1 * (params.nextX + 1) ≤ (8 * C) * params.tailBlock.card := by
  let : NeZero params.Mplus := by
    dsimp [StageParams.Mplus]
    infer_instance
  have hKX : params.K ≤ params.nextX := by
    rw [StageParams.nextX]
    omega
  have htail_lower : params.Dplus.card * (params.LZ / params.Mplus) ≤
      params.tailBlock.card := by
    have hcount := residueBlockFinset_card_lower_of_le params.Mplus params.Dplus hKX
    simpa [StageParams.tailBlock, StageParams.nextX, StageParams.Mplus] using hcount
  have hmain : params.nextX + 1 ≤
      8 * C * (params.Dplus.card * (params.LZ / params.Mplus)) := by
    exact nat_le_eight_mul_of_floor_density (M := params.Mplus) (C := C)
      (card := params.Dplus.card) (len := params.LZ) (endpoint := params.nextX + 1)
      (NeZero.pos params.Mplus) hMle hlen
  nlinarith

theorem StageParams.exists_protectedSubblock_bounds_of_standardN_gap
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P)
    (hN_eq : params.N = st.X + 1)
    (hML : params.Mplus ≤ params.L)
    (hgap :
      st.X + params.N + params.L + params.Mplus + 1 < params.protectedEndpoint) :
    ∃ lo hi : ℕ,
      lo ≤ hi ∧
      2 * params.N + params.Mplus - a ≤ lo ∧
      hi ≤ params.serviceR - a ∧
      st.X + params.N + params.L < a + lo ∧
      a + hi < params.protectedEndpoint ∧
      params.Mplus ≤ hi - lo := by
  let lo := st.X + params.N + params.L + 1 - a
  let hi := lo + params.Mplus
  have haX : a ≤ st.X := st.active_le_X ha
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [lo, hi]
    simp only [hN_eq, StageParams.protectedEndpoint] at hgap ⊢
    omega

theorem StageParams.exists_protectedSubblock_bounds_of_standardN_longGap
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P)
    (hN_eq : params.N = st.X + 1)
    (hML : params.Mplus ≤ params.L)
    (hlong :
      params.protectedEndpoint + 4 * params.Mplus +
          4 * (st.X + params.N + params.L + 2) ≤
        4 * params.protectedEndpoint) :
    ∃ lo hi : ℕ,
      lo ≤ hi ∧
      2 * params.N + params.Mplus - a ≤ lo ∧
      hi ≤ params.serviceR - a ∧
      st.X + params.N + params.L < a + lo ∧
      a + hi < params.protectedEndpoint ∧
      params.protectedEndpoint + 4 * params.Mplus ≤ 4 * (hi - lo) := by
  let lo := st.X + params.N + params.L + 1 - a
  let hi := params.protectedEndpoint - a - 1
  have haX : a ≤ st.X := st.active_le_X ha
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [lo, hi]
    simp only [hN_eq, StageParams.protectedEndpoint] at hlong ⊢
    omega

theorem StageParams.Pstar_card_pos
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    0 < params.G.Pstar.card := by
  refine params.G.Pstar_card_pos (activatedM_pos st hbDormant hp)
    ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos) ?_
  intro c hc
  have hcActive : c ∈ activatedActiveSet st b := (Finset.mem_erase.mp hc).2
  have hge := activated_m_ge23 st hbDormant hp c hcActive
  omega

theorem StageParams.Mplus_le_two_mul_selected_mul_Pstar_card_of_budget
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ)) :
    params.Mplus ≤ 2 * activatedModulus st b p a * params.G.Pstar.card := by
  simpa [StageParams.Mplus] using
    params.G.M_le_two_mul_selected_mul_Pstar_card
      (activatedM_pos st hbDormant hp)
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
      (fun c hc => (activated_m_prime st hbDormant hp c (Finset.mem_erase.mp hc).2).pos)
      hbudget

theorem StageParams.tailBlock_fixedDensity_of_budget
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ))
    (hlen : params.nextX + 1 + 4 * params.Mplus ≤ 4 * params.LZ) :
    1 * (params.nextX + 1) ≤
      (8 * activatedModulus st b p a) * params.tailBlock.card := by
  have hcard_le : params.G.Pstar.card ≤ params.Dplus.card :=
    Finset.card_le_card params.G.Pstar_subset_D
  have hMleP := params.Mplus_le_two_mul_selected_mul_Pstar_card_of_budget
    ha hbDormant hp hbudget
  have hMleD :
      params.Mplus ≤ 2 * activatedModulus st b p a * params.Dplus.card := by
    exact hMleP.trans (by
      have hmul := Nat.mul_le_mul_left (2 * activatedModulus st b p a) hcard_le
      simpa [Nat.mul_assoc] using hmul)
  exact params.tailBlock_fixedDensity_arithmetic
    (C := activatedModulus st b p a) hMleD hlen

theorem StageState.erase_budget_lt_of_strict
    {st : StageState} {a : ℕ} (hbudget : st.HasStrictReciprocalBudget) :
    (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) < (1 / 2 : ℝ) := by
  have herase_subset : st.P.erase a ⊆ st.P := Finset.erase_subset a st.P
  have hle :
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) ≤
        st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg herase_subset
      (by
        intro c _hcP _hcErase
        positivity)
  exact hle.trans_lt hbudget

theorem activated_budget_total_eq {st : StageState} {b p : ℕ}
    (hbDormant : b ∉ st.P) :
    (activatedActiveSet st b).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) =
      st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p := by
  rw [activatedActiveSet, Finset.sum_insert hbDormant]
  rw [activatedModulus_new]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [activatedModulus_old_of_mem st hbDormant hc]

theorem activated_erase_budget_le_total {st : StageState} {a b p : ℕ} :
    ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤
      (activatedActiveSet st b).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) := by
  have herase_subset : (activatedActiveSet st b).erase a ⊆ activatedActiveSet st b :=
    Finset.erase_subset a (activatedActiveSet st b)
  exact Finset.sum_le_sum_of_subset_of_nonneg herase_subset
    (by
      intro c _hcP _hcErase
      positivity)

theorem exists_freshPrimeData_preserving_strictBudget
    {st : StageState} {b : ℕ} (hbDormant : b ∉ st.P)
    (hbudget : st.HasStrictReciprocalBudget) :
    ∃ p : ℕ, FreshPrimeData st p ∧
      (activatedActiveSet st b).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) < (1 / 2 : ℝ) := by
  obtain ⟨N, hNpos, hbudgetN⟩ := exists_nat_reciprocal_budget_strict hbudget
  obtain ⟨p, hNp, hp⟩ := exists_freshPrimeData_ge st N
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNpR : (N : ℝ) ≤ p := by exact_mod_cast hNp
  have hpfrac : (1 : ℝ) / p ≤ (1 : ℝ) / N :=
    one_div_le_one_div_of_le hNposR hNpR
  have hbudget_p :
      st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p <
        (1 / 2 : ℝ) := by
    have hstep :
        st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p ≤
          st.P.sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / N := by
      linarith
    exact hstep.trans_lt hbudgetN
  refine ⟨p, hp, ?_⟩
  rwa [activated_budget_total_eq hbDormant]

theorem activated_budget_erase_eq {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) :
    ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) =
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p := by
  have hba : b ≠ a := by
    intro h
    exact hbDormant (h.symm ▸ ha)
  have hbErase : b ∉ st.P.erase a := by
    intro hb
    exact hbDormant (Finset.mem_erase.mp hb).2
  rw [activatedActiveSet, Finset.erase_insert_of_ne hba]
  rw [Finset.sum_insert hbErase]
  rw [activatedModulus_new]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [activatedModulus_old_of_mem st hbDormant (Finset.mem_erase.mp hc).2]

theorem exists_freshPrimeData_with_activated_budget_of_bound
    {st : StageState} {a b N : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hNpos : 0 < N)
    (hbudgetN :
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / N ≤
        (1 / 2 : ℝ)) :
    ∃ p : ℕ, FreshPrimeData st p ∧
      ((activatedActiveSet st b).erase a).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ) := by
  obtain ⟨p, hNp, hp⟩ := exists_freshPrimeData_ge st N
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNpR : (N : ℝ) ≤ p := by exact_mod_cast hNp
  have hpfrac : (1 : ℝ) / p ≤ (1 : ℝ) / N :=
    one_div_le_one_div_of_le hNposR hNpR
  have hbudget :
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p ≤
        (1 / 2 : ℝ) := by
    have hstep :
        (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / p ≤
          (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / N := by
      linarith
    exact hstep.trans hbudgetN
  refine ⟨p, hp, ?_⟩
  rwa [activated_budget_erase_eq ha hbDormant]

theorem exists_freshPrimeData_with_activated_budget_of_strict
    {st : StageState} {a b : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (hbudget_lt :
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) < (1 / 2 : ℝ)) :
    ∃ p : ℕ, FreshPrimeData st p ∧
      ((activatedActiveSet st b).erase a).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ) := by
  obtain ⟨N, hNpos, hbudgetN⟩ := exists_nat_reciprocal_budget_bound hbudget_lt
  exact exists_freshPrimeData_with_activated_budget_of_bound ha hbDormant hNpos hbudgetN

/--
Full canonical service step from the bundled arithmetic inequalities.

This packages the standard residue-lift coverage argument, the protected-block
privacy proof, the density subblock estimate, and preservation of the canonical
reservoir residues into one interface.
-/
noncomputable def canonicalServiceExtensionOfParamsFromCoreAndTbaseEq
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hcore : params.CoreInequalities)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    CanonicalServiceExtension st a := by
  have hD : st.D = stageCRTAllowedFinsetAtM st ha := hCanon a ha
  have hD_add :
      ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ := by
    rw [hD]
    exact stageCRTAllowedFinsetAtM_add_self_eq_univ st ha
  have hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ := by
    rw [hDplus]
    exact activatedCRTAllowedFinsetAtM_add_self_eq_univ st ha hbDormant hp
  have hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b :=
    params.exists_dormant_from_tail_of_Dplus_add_self hbS hcore.hK hcore.hMLZ hDplus_add
  exact serviceExtensionOfParamsWithCanonicalD params ha hbS hbDormant hp hDplus
    hcore.hN hcore.hK hcore.hX_next hcore.hR_next hcore.hlower_height
    hcore.hprivate_height params.nextS_new_elements_avoid_active
    hcore.hreservoir_long hcore.hheadroom
    (stageParams_nextS_coverage_of_helpers params ha hcore.hN
      (stageParams_T_helper_of_old_residue_lift params hp
        (stageParams_T_lift_of_canonicalD_stageTbase_eq_activated params ha hbDormant hp
          hD h u1 u2 hTbase))
      (stageParams_D_helper_of_old_residue_lift params hp
        (stageParams_D_lift_of_oldD_add_canonicalDplus params ha hbDormant hp hDplus hD_add))
      hDplus_add
      hcore.hCL hcore.hlower_start hcore.hlower_end hcore.hML hcore.hCLZ
      hcore.htail_start hcore.htail_end hcore.hMLZ)
    hexists_dormant hcore.hendpoint_le_nextX hdensityDenominator_pos
    (params.protectedSumBlock_private ha hbDormant hcore.hN)
    (params.protectedSumBlock_density_of_residue_subblock (lo := lo) (hi := hi)
      hlohi hlo_private hhi_private hlo_sum hhi_sum harith)

/--
Canonical service step where density is supplied by any protected subblock of
length at least one full new modulus and a nonempty private residue set.
-/
noncomputable def canonicalServiceExtensionOfParamsFromCoreAndTbaseEqWithDensityBounds
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hcore : params.CoreInequalities)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (hMle : params.Mplus ≤ hi - lo) :
    CanonicalServiceExtension st a :=
  canonicalServiceExtensionOfParamsFromCoreAndTbaseEq params ha hbS hbDormant hp hCanon
    hDplus h u1 u2 hTbase hcore (densityNumerator := 1)
    (densityDenominator := params.protectedEndpoint + 1)
    (by omega) hlohi hlo_private hhi_private hlo_sum hhi_sum
    (params.protectedSubblock_density_arithmetic
      (params.Pstar_card_pos ha hbDormant hp) hMle)

/--
Canonical service step with a fixed density denominator, assuming the standard
active-modulus budget and a protected subblock long enough to absorb the floor
in the residue-block count.
-/
noncomputable def canonicalServiceExtensionOfParamsFromCoreAndTbaseEqWithBudgetDensity
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hcore : params.CoreInequalities)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ))
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (hlen : params.protectedEndpoint + 4 * params.Mplus ≤ 4 * (hi - lo)) :
    CanonicalServiceExtension st a :=
  canonicalServiceExtensionOfParamsFromCoreAndTbaseEq params ha hbS hbDormant hp hCanon
    hDplus h u1 u2 hTbase hcore (densityNumerator := 1)
    (densityDenominator := 8 * activatedModulus st b p a)
    (by
      have hpos := (activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos
      omega)
    hlohi hlo_private hhi_private hlo_sum hhi_sum
    (params.protectedSubblock_fixedDensity_arithmetic
      (C := activatedModulus st b p a)
      (params.Mplus_le_two_mul_selected_mul_Pstar_card_of_budget ha hbDormant hp hbudget)
      hlen)

/--
Variant of `canonicalServiceExtensionOfParamsFromCoreAndTbaseEq` for the
standard choice `N = X + 1` and explicit large-length hypotheses.
-/
noncomputable def canonicalServiceExtensionOfParamsFromStandardNAndTbaseEq
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hN_eq : params.N = st.X + 1)
    (hL_service : params.Mplus + 3 * st.M ≤ params.L)
    (hR_service : st.R ≤ params.serviceR)
    (hLZ_private : st.X ≤ params.LZ)
    (hLZ_headroom : 4 * params.Mplus ≤ params.LZ)
    (hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    CanonicalServiceExtension st a :=
  canonicalServiceExtensionOfParamsFromCoreAndTbaseEq params ha hbS hbDormant hp hCanon
    hDplus h u1 u2 hTbase
    (StageParams.coreInequalities_of_standardN_large params hN_eq hL_service hR_service
      hLZ_private hLZ_headroom hLZ_tail)
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

/--
Standard service wrapper with all routine arithmetic and density bookkeeping
discharged from large-length and protected-gap hypotheses.
-/
noncomputable def canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithDensityGap
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hN_eq : params.N = st.X + 1)
    (hL_service : params.Mplus + 3 * st.M ≤ params.L)
    (hR_service : st.R ≤ params.serviceR)
    (hLZ_private : st.X ≤ params.LZ)
    (hLZ_headroom : 4 * params.Mplus ≤ params.LZ)
    (hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ)
    (hgap :
      st.X + params.N + params.L + params.Mplus + 1 < params.protectedEndpoint) :
    CanonicalServiceExtension st a := by
  have hcore :=
    StageParams.coreInequalities_of_standardN_large params hN_eq hL_service hR_service
      hLZ_private hLZ_headroom hLZ_tail
  have hML : params.Mplus ≤ params.L := by omega
  let hbounds := params.exists_protectedSubblock_bounds_of_standardN_gap ha hN_eq hML hgap
  let lo := Classical.choose hbounds
  let hbounds_hi := Classical.choose_spec hbounds
  let hi := Classical.choose hbounds_hi
  have hspec := Classical.choose_spec hbounds_hi
  exact canonicalServiceExtensionOfParamsFromCoreAndTbaseEqWithDensityBounds params
    ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbase hcore hspec.1 hspec.2.1
    hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.1 hspec.2.2.2.2.2

/--
Standard service wrapper with fixed density denominator `8 * m(a)`, assuming
the active reciprocal budget and a protected core long enough for the floor
loss in residue counting.
-/
noncomputable def canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithBudgetLongGap
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hCanon : st.HasCanonicalD)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hN_eq : params.N = st.X + 1)
    (hL_service : params.Mplus + 3 * st.M ≤ params.L)
    (hR_service : st.R ≤ params.serviceR)
    (hLZ_private : st.X ≤ params.LZ)
    (hLZ_headroom : 4 * params.Mplus ≤ params.LZ)
    (hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ))
    (hlong :
      params.protectedEndpoint + 4 * params.Mplus +
          4 * (st.X + params.N + params.L + 2) ≤
        4 * params.protectedEndpoint) :
    CanonicalServiceExtension st a := by
  have hcore :=
    StageParams.coreInequalities_of_standardN_large params hN_eq hL_service hR_service
      hLZ_private hLZ_headroom hLZ_tail
  have hML : params.Mplus ≤ params.L := by omega
  let hbounds :=
    params.exists_protectedSubblock_bounds_of_standardN_longGap ha hN_eq hML hlong
  let lo := Classical.choose hbounds
  let hbounds_hi := Classical.choose_spec hbounds
  let hi := Classical.choose hbounds_hi
  have hspec := Classical.choose_spec hbounds_hi
  exact canonicalServiceExtensionOfParamsFromCoreAndTbaseEqWithBudgetDensity params
    ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbase hcore hbudget hspec.1
    hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.1 hspec.2.2.2.2.2

theorem exists_canonicalServiceExtension_of_active_dormant_fresh
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD) :
    Nonempty (CanonicalServiceExtension st a) := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  obtain ⟨h, u1, u2, G, _hT, _hPstar, hTbase⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  let Mnew := activatedM st b p
  let N := st.X + 1
  let L := st.X + 2 * Mnew + st.R + 3 * st.M + 1
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params := stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ
  have hDplus :
      params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp :=
    stageParamsOfActivatedExactGadget_Dplus_eq st ha hbDormant hp G N L LZ
  have hTbaseAtM :
      params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 :=
    stageParamsOfActivatedExactGadget_Tbase_eq st ha hbDormant hp G N L LZ
      h u1 u2 hTbase
  have hN_eq : params.N = st.X + 1 := by
    dsimp [params, stageParamsOfActivatedExactGadget, N]
  have hL_service : params.Mplus + 3 * st.M ≤ params.L := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.Mplus, Mnew]
    omega
  have hR_service : st.R ≤ params.serviceR := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.serviceR,
      StageParams.Mplus, Mnew, N]
    apply Nat.le_sub_of_add_le
    omega
  have hLZ_private : st.X ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ]
    omega
  have hLZ_headroom : 4 * params.Mplus ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, StageParams.Mplus, Mnew]
    omega
  have hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, L]
    omega
  have hgap :
      st.X + params.N + params.L + params.Mplus + 1 < params.protectedEndpoint := by
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  exact ⟨canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithDensityGap params
    ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbaseAtM hN_eq hL_service hR_service
    hLZ_private hLZ_headroom hLZ_tail hgap⟩

theorem exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ)) :
    Nonempty (CanonicalServiceExtension st a) := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  obtain ⟨h, u1, u2, G, _hT, _hPstar, hTbase⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  let Mnew := activatedM st b p
  let N := st.X + 1
  let L := 3 * st.X + 4 * Mnew + st.R + 3 * st.M + 10
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params := stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ
  have hDplus :
      params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp :=
    stageParamsOfActivatedExactGadget_Dplus_eq st ha hbDormant hp G N L LZ
  have hTbaseAtM :
      params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 :=
    stageParamsOfActivatedExactGadget_Tbase_eq st ha hbDormant hp G N L LZ
      h u1 u2 hTbase
  have hN_eq : params.N = st.X + 1 := by
    dsimp [params, stageParamsOfActivatedExactGadget, N]
  have hL_service : params.Mplus + 3 * st.M ≤ params.L := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.Mplus, Mnew]
    omega
  have hR_service : st.R ≤ params.serviceR := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.serviceR,
      StageParams.Mplus, Mnew, N]
    apply Nat.le_sub_of_add_le
    omega
  have hLZ_private : st.X ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ]
    omega
  have hLZ_headroom : 4 * params.Mplus ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, StageParams.Mplus, Mnew]
    omega
  have hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, L]
    omega
  have hlong :
      params.protectedEndpoint + 4 * params.Mplus +
          4 * (st.X + params.N + params.L + 2) ≤
        4 * params.protectedEndpoint := by
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  exact ⟨canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithBudgetLongGap params
    ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbaseAtM hN_eq hL_service hR_service
    hLZ_private hLZ_headroom hLZ_tail hbudget hlong⟩

theorem exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget_ge
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ))
    (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          svc.service.protectedBlock.densityNumerator = 1 ∧
            svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
              svc.next.P = activatedActiveSet st b ∧
                svc.next.m = activatedModulus st b p := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  obtain ⟨h, u1, u2, G, _hT, _hPstar, hTbase⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  let Mnew := activatedM st b p
  let N := st.X + 1
  let L := 3 * st.X + 4 * Mnew + st.R + 3 * st.M + 10 + B
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params := stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ
  have hDplus :
      params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp :=
    stageParamsOfActivatedExactGadget_Dplus_eq st ha hbDormant hp G N L LZ
  have hTbaseAtM :
      params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 :=
    stageParamsOfActivatedExactGadget_Tbase_eq st ha hbDormant hp G N L LZ
      h u1 u2 hTbase
  have hN_eq : params.N = st.X + 1 := by
    dsimp [params, stageParamsOfActivatedExactGadget, N]
  have hL_service : params.Mplus + 3 * st.M ≤ params.L := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.Mplus, Mnew]
    omega
  have hR_service : st.R ≤ params.serviceR := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.serviceR,
      StageParams.Mplus, Mnew, N]
    apply Nat.le_sub_of_add_le
    omega
  have hLZ_private : st.X ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ]
    omega
  have hLZ_headroom : 4 * params.Mplus ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, StageParams.Mplus, Mnew]
    omega
  have hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, L]
    omega
  have hlong :
      params.protectedEndpoint + 4 * params.Mplus +
          4 * (st.X + params.N + params.L + 2) ≤
        4 * params.protectedEndpoint := by
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  let svc :=
    canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithBudgetLongGap params
      ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbaseAtM hN_eq hL_service hR_service
      hLZ_private hLZ_headroom hLZ_tail hbudget hlong
  refine ⟨svc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change B ≤ params.protectedEndpoint
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  · change B ≤ params.nextR
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, LZ, StageParams.nextR,
      StageParams.nextX, StageParams.K, StageParams.protectedEndpoint, StageParams.serviceR,
      StageParams.Mplus, Mnew]
    omega
  · rfl
  · calc
      svc.service.protectedBlock.densityDenominator = 8 * activatedModulus st b p a := rfl
      _ = 8 * st.m a := by rw [activatedModulus_old_of_mem st hbDormant ha]
  · rfl
  · rfl

theorem exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget_ge_and_stageBlock
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD)
    (hbudget :
      ((activatedActiveSet st b).erase a).sum
        (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ))
    (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a, ∃ endpoint : ℕ, ∃ block : Finset ℕ,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          B ≤ endpoint ∧
            (∀ n ∈ block, n ∈ svc.next.S ∧ n < endpoint) ∧
              1 * endpoint ≤ (8 * st.m a) * block.card ∧
                svc.service.protectedBlock.densityNumerator = 1 ∧
                  svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
                    svc.next.P = activatedActiveSet st b ∧
                      svc.next.m = activatedModulus st b p := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  obtain ⟨h, u1, u2, G, _hT, _hPstar, hTbase⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  let Mnew := activatedM st b p
  let N := st.X + 1
  let L := 3 * st.X + 4 * Mnew + st.R + 3 * st.M + 10 + B
  let LZ := 2 * L + 4 * Mnew + 3 * st.M + st.X + 2
  let params := stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ
  have hDplus :
      params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp :=
    stageParamsOfActivatedExactGadget_Dplus_eq st ha hbDormant hp G N L LZ
  have hTbaseAtM :
      params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 :=
    stageParamsOfActivatedExactGadget_Tbase_eq st ha hbDormant hp G N L LZ
      h u1 u2 hTbase
  have hN_eq : params.N = st.X + 1 := by
    dsimp [params, stageParamsOfActivatedExactGadget, N]
  have hL_service : params.Mplus + 3 * st.M ≤ params.L := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.Mplus, Mnew]
    omega
  have hR_service : st.R ≤ params.serviceR := by
    dsimp [params, stageParamsOfActivatedExactGadget, L, StageParams.serviceR,
      StageParams.Mplus, Mnew, N]
    apply Nat.le_sub_of_add_le
    omega
  have hLZ_private : st.X ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ]
    omega
  have hLZ_headroom : 4 * params.Mplus ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, StageParams.Mplus, Mnew]
    omega
  have hLZ_tail : 2 * params.L + 3 * st.M + 2 ≤ params.LZ := by
    dsimp [params, stageParamsOfActivatedExactGadget, LZ, L]
    omega
  have hlong :
      params.protectedEndpoint + 4 * params.Mplus +
          4 * (st.X + params.N + params.L + 2) ≤
        4 * params.protectedEndpoint := by
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  let svc :=
    canonicalServiceExtensionOfParamsFromStandardNAndTbaseEqWithBudgetLongGap params
      ha hbS hbDormant hp hCanon hDplus h u1 u2 hTbaseAtM hN_eq hL_service hR_service
      hLZ_private hLZ_headroom hLZ_tail hbudget hlong
  refine ⟨svc, params.nextX + 1, params.tailBlock, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change B ≤ params.protectedEndpoint
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, StageParams.protectedEndpoint,
      StageParams.serviceR, StageParams.Mplus, Mnew]
    omega
  · change B ≤ params.nextR
    dsimp [params, stageParamsOfActivatedExactGadget, N, L, LZ, StageParams.nextR,
      StageParams.nextX, StageParams.K, StageParams.protectedEndpoint, StageParams.serviceR,
      StageParams.Mplus, Mnew]
    omega
  · dsimp [params, stageParamsOfActivatedExactGadget, N, L, LZ, StageParams.nextX,
      StageParams.K, StageParams.protectedEndpoint, StageParams.serviceR,
      StageParams.Mplus, Mnew]
    omega
  · intro n hn
    constructor
    · change n ∈ params.nextS
      exact params.tailBlock_subset_nextS hn
    · rw [StageParams.mem_tailBlock] at hn
      omega
  · have htailLen : params.nextX + 1 + 4 * params.Mplus ≤ 4 * params.LZ := by
      dsimp [params, stageParamsOfActivatedExactGadget, N, L, LZ, StageParams.nextX,
        StageParams.K, StageParams.protectedEndpoint, StageParams.serviceR,
        StageParams.Mplus, Mnew]
      omega
    have hdensity :=
      params.tailBlock_fixedDensity_of_budget ha hbDormant hp hbudget htailLen
    simpa [activatedModulus_old_of_mem st hbDormant ha] using hdensity
  · rfl
  · calc
      svc.service.protectedBlock.densityDenominator = 8 * activatedModulus st b p a := rfl
      _ = 8 * st.m a := by rw [activatedModulus_old_of_mem st hbDormant ha]
  · rfl
  · rfl

theorem exists_canonicalServiceExtension_of_active_dormant_with_budget_bound
    {st : StageState} {a b N : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hCanon : st.HasCanonicalD) (hNpos : 0 < N)
    (hbudgetN :
      (st.P.erase a).sum (fun c => (1 : ℝ) / (st.m c : ℝ)) + (1 : ℝ) / N ≤
        (1 / 2 : ℝ)) :
    Nonempty (CanonicalServiceExtension st a) := by
  obtain ⟨p, hp, hbudget⟩ :=
    exists_freshPrimeData_with_activated_budget_of_bound ha hbDormant hNpos hbudgetN
  exact exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget ha hbS
    hbDormant hp hCanon hbudget

theorem exists_canonicalServiceExtension_of_active_dormant_fresh_preserving_strictBudget_ge
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD)
    (hactivatedBudget :
      (activatedActiveSet st b).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) < (1 / 2 : ℝ))
    (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          svc.service.protectedBlock.densityNumerator = 1 ∧
            svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
              svc.next.HasStrictReciprocalBudget := by
  have hbudget_erase :
      ((activatedActiveSet st b).erase a).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ) :=
    (activated_erase_budget_le_total (st := st) (a := a) (b := b) (p := p)).trans
      hactivatedBudget.le
  obtain ⟨svc, hendpoint, hR, hnum, hden, hP, hm⟩ :=
    exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget_ge ha hbS
      hbDormant hp hCanon hbudget_erase B
  refine ⟨svc, hendpoint, hR, hnum, hden, ?_⟩
  dsimp [StageState.HasStrictReciprocalBudget]
  rw [hP, hm]
  exact hactivatedBudget

theorem exists_canonicalServiceExtension_of_active_dormant_fresh_preserving_strictBudget_ge_and_stageBlock
    {st : StageState} {a b p : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) (hCanon : st.HasCanonicalD)
    (hactivatedBudget :
      (activatedActiveSet st b).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) < (1 / 2 : ℝ))
    (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a, ∃ endpoint : ℕ, ∃ block : Finset ℕ,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          B ≤ endpoint ∧
            (∀ n ∈ block, n ∈ svc.next.S ∧ n < endpoint) ∧
              1 * endpoint ≤ (8 * st.m a) * block.card ∧
                svc.service.protectedBlock.densityNumerator = 1 ∧
                  svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
                    svc.next.HasStrictReciprocalBudget := by
  have hbudget_erase :
      ((activatedActiveSet st b).erase a).sum
          (fun c => (1 : ℝ) / (activatedModulus st b p c : ℝ)) ≤ (1 / 2 : ℝ) :=
    (activated_erase_budget_le_total (st := st) (a := a) (b := b) (p := p)).trans
      hactivatedBudget.le
  obtain ⟨svc, endpoint, block, hprot, hR, hBendpoint, hblock, hdensity, hnum, hden, hP, hm⟩ :=
    exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget_ge_and_stageBlock
      ha hbS hbDormant hp hCanon hbudget_erase B
  refine ⟨svc, endpoint, block, hprot, hR, hBendpoint, hblock, hdensity, hnum, hden, ?_⟩
  dsimp [StageState.HasStrictReciprocalBudget]
  rw [hP, hm]
  exact hactivatedBudget

theorem exists_canonicalServiceExtension_of_active_dormant_preserving_strictBudget_ge
    {st : StageState} {a b : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hCanon : st.HasCanonicalD) (hbudget : st.HasStrictReciprocalBudget) (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          svc.service.protectedBlock.densityNumerator = 1 ∧
            svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
              svc.next.HasStrictReciprocalBudget := by
  obtain ⟨p, hp, hactivatedBudget⟩ :=
    exists_freshPrimeData_preserving_strictBudget hbDormant hbudget
  exact exists_canonicalServiceExtension_of_active_dormant_fresh_preserving_strictBudget_ge
    ha hbS hbDormant hp hCanon hactivatedBudget B

theorem exists_canonicalServiceExtension_of_active_dormant_preserving_strictBudget_ge_and_stageBlock
    {st : StageState} {a b : ℕ}
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hCanon : st.HasCanonicalD) (hbudget : st.HasStrictReciprocalBudget) (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a, ∃ endpoint : ℕ, ∃ block : Finset ℕ,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          B ≤ endpoint ∧
            (∀ n ∈ block, n ∈ svc.next.S ∧ n < endpoint) ∧
              1 * endpoint ≤ (8 * st.m a) * block.card ∧
                svc.service.protectedBlock.densityNumerator = 1 ∧
                  svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
                    svc.next.HasStrictReciprocalBudget := by
  obtain ⟨p, hp, hactivatedBudget⟩ :=
    exists_freshPrimeData_preserving_strictBudget hbDormant hbudget
  exact exists_canonicalServiceExtension_of_active_dormant_fresh_preserving_strictBudget_ge_and_stageBlock
    ha hbS hbDormant hp hCanon hactivatedBudget B

theorem exists_canonicalServiceExtension_of_active_preserving_strictBudget_ge
    {st : StageState} {a : ℕ}
    (ha : a ∈ st.P) (hCanon : st.HasCanonicalD)
    (hbudget : st.HasStrictReciprocalBudget) (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          svc.service.protectedBlock.densityNumerator = 1 ∧
            svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
              svc.next.HasStrictReciprocalBudget := by
  obtain ⟨b, hbS, hbDormant⟩ := st.exists_dormant
  exact exists_canonicalServiceExtension_of_active_dormant_preserving_strictBudget_ge
    ha hbS hbDormant hCanon hbudget B

theorem exists_canonicalServiceExtension_of_active_preserving_strictBudget_ge_and_stageBlock
    {st : StageState} {a : ℕ}
    (ha : a ∈ st.P) (hCanon : st.HasCanonicalD)
    (hbudget : st.HasStrictReciprocalBudget) (B : ℕ) :
    ∃ svc : CanonicalServiceExtension st a, ∃ endpoint : ℕ, ∃ block : Finset ℕ,
      B ≤ svc.service.protectedEndpoint ∧
        B ≤ svc.next.R ∧
          B ≤ endpoint ∧
            (∀ n ∈ block, n ∈ svc.next.S ∧ n < endpoint) ∧
              1 * endpoint ≤ (8 * st.m a) * block.card ∧
                svc.service.protectedBlock.densityNumerator = 1 ∧
                  svc.service.protectedBlock.densityDenominator = 8 * st.m a ∧
                    svc.next.HasStrictReciprocalBudget := by
  obtain ⟨b, hbS, hbDormant⟩ := st.exists_dormant
  exact exists_canonicalServiceExtension_of_active_dormant_preserving_strictBudget_ge_and_stageBlock
    ha hbS hbDormant hCanon hbudget B

theorem initialStageState_hasStrictReciprocalBudget (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) :
    (initialStageState a m H X hmPrime hm23 hmMod4 haX hlong).HasStrictReciprocalBudget := by
  dsimp [StageState.HasStrictReciprocalBudget, initialStageState]
  simp
  have hmgt2 : (2 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 2 < 23) hm23)
  simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hmgt2

theorem exists_initialStageState_with_strictBudget :
    ∃ st : StageState, st.HasCanonicalD ∧ st.HasStrictReciprocalBudget := by
  obtain ⟨m, hm23, hmPrime, hmMod4⟩ := exists_prime_three_mod_four_ge 23
  let H := m + 2
  let X := H + 4 * m
  refine ⟨initialStageState 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega), ?_, ?_⟩
  · exact initialStageState_hasCanonicalD 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega)
  · exact initialStageState_hasStrictReciprocalBudget 1 m H X hmPrime hm23 hmMod4
      (by omega) (by omega)

theorem exists_canonicalServiceExtension_of_active
    {st : StageState} {a : ℕ}
    (ha : a ∈ st.P) (hCanon : st.HasCanonicalD) :
    Nonempty (CanonicalServiceExtension st a) := by
  obtain ⟨b, hbS, hbDormant⟩ := st.exists_dormant
  obtain ⟨p, hp⟩ := exists_freshPrimeData st
  exact exists_canonicalServiceExtension_of_active_dormant_fresh ha hbS hbDormant hp hCanon

end Erdos330
