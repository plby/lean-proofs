/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.PredecessorClique
import ErdosProblems.Erdos518.MuBound
import ErdosProblems.Erdos518.DenseBipartite
import ErdosProblems.Erdos518.CoverDevice
import ErdosProblems.Erdos518.CaseArithmetic

/-!
# Claim 1 in the Chen--Chen argument

This file excludes the branch
`c + 1 ≤ a0 + ceilHalf a1` when `4 ≤ c`.  The preceding predecessor-clique
argument supplies the single structural input `mu ≤ r - 2`; keeping that
input explicit makes the dependency between the two claims transparent.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance claimOneDecidableEq : DecidableEq V := Classical.decEq V

private lemma claimOne_dense_degree (hmu : C.mu ≤ C.r - 2) (hc : 4 ≤ C.c) :
    ∀ y ∈ C.Y, C.X.card + C.Y.card ≤ 2 * C.redDegreeToX y := by
  intro y hy
  have hw := C.w_le_r_sub_two
  have hr := C.r_le_two_mul_c
  have hw_add : C.w + 2 ≤ C.r := by
    have := C.w_ge_c
    omega
  have hmu_add : C.mu + 2 ≤ C.r := by
    have := C.w_ge_c
    omega
  have hwZ : (C.w : ℤ) ≤ (C.r : ℤ) - 2 := by
    have hwAddZ : (C.w : ℤ) + 2 ≤ (C.r : ℤ) := by exact_mod_cast hw_add
    omega
  have hmuZ : (C.mu : ℤ) ≤ (C.r : ℤ) - 2 := by
    have hmuAddZ : (C.mu : ℤ) + 2 ≤ (C.r : ℤ) := by exact_mod_cast hmu_add
    omega
  have hnonnegZ := claim1_dense_nonneg
    (c := (C.c : ℤ)) (r := (C.r : ℤ)) (w := (C.w : ℤ)) (μ := (C.mu : ℤ))
    (by exact_mod_cast hc) (by exact_mod_cast hr) hwZ hmuZ
  have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, ← C.n_eq_c_sq_add_r]
  have hblue := C.blueDegreeToX_le_mu_of_mem_Y hy
  have hdegree := C.redDegreeToX_add_blueDegreeToX hy
  rw [← C.w_eq_card_Y]
  have hsumZ : (C.X.card : ℤ) + (C.w : ℤ) =
      (C.c : ℤ) ^ 2 + (C.r : ℤ) := by exact_mod_cast hsum
  have hblueZ : (C.blueDegreeToX y : ℤ) ≤ (C.mu : ℤ) := by
    exact_mod_cast hblue
  have hdegreeZ : (C.redDegreeToX y : ℤ) + (C.blueDegreeToX y : ℤ) =
      (C.X.card : ℤ) := by exact_mod_cast hdegree
  have hgoalZ : (C.X.card : ℤ) + (C.w : ℤ) ≤
      2 * (C.redDegreeToX y : ℤ) := by omega
  exact_mod_cast hgoalZ

private lemma claimOne_dense_path (hmu : C.mu ≤ C.r - 2) (hc : 4 ≤ C.c) :
    ∃ P : List V,
      IsPath C.G P ∧
      P.length = 2 * C.w ∧
      (∀ v ∈ P, v ∈ C.X ∪ C.Y) ∧
      (∀ y ∈ C.Y, y ∈ P) ∧
      (P.toFinset ∩ C.X).card = C.w := by
  have hY : C.Y.Nonempty := by
    apply Finset.card_pos.mp
    rw [← C.w_eq_card_Y]
    exact lt_of_lt_of_le (by omega) C.w_ge_c
  simpa [C.w_eq_card_Y] using
    (exists_path_of_dense_bipartite C.G C.X C.Y C.X_disjoint_Y hY
      (C.claimOne_dense_degree hmu hc))

private lemma claimOne_sparse_Y1 :
    ∀ y ∈ C.Y1, (nonRedNeighboursIn C.G C.X y).card ≤ C.mu := by
  classical
  intro y hy
  have hyY : y ∈ C.Y := C.Y1_subset_Y hy
  have heq : nonRedNeighboursIn C.G C.X y =
      C.X.filter (fun x ↦ C.Gᶜ.Adj y x) := by
    rw [nonRedNeighboursIn]
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hnot⟩
      refine ⟨hx, (SimpleGraph.compl_adj C.G y x).mpr ⟨?_, hnot⟩⟩
      intro hyx
      subst x
      exact (C.mem_Y.mp hyY) hx
    · rintro ⟨hx, hblue⟩
      exact ⟨hx, ((SimpleGraph.compl_adj C.G y x).mp hblue).2⟩
  rw [heq]
  exact C.blueDegreeToX_le_mu_of_mem_Y1 hy

private lemma claimOne_path_union_remainder
    {P : List V} (hPY : ∀ y ∈ C.Y, y ∈ P) :
    P.toFinset ∪ (C.X \ P.toFinset) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  by_cases hvP : v ∈ P
  · exact Finset.mem_union_left _ (by simpa using hvP)
  · apply Finset.mem_union_right
    refine Finset.mem_sdiff.mpr ⟨?_, by simpa using hvP⟩
    by_contra hvX
    have hvY : v ∈ C.Y := C.mem_Y.mpr hvX
    exact hvP (hPY v hvY)

private lemma claimOne_remainder_card
    {P : List V} (hPX : (P.toFinset ∩ C.X).card = C.w) :
    (C.X \ P.toFinset).card = C.c ^ 2 + C.r - 2 * C.w := by
  have hinter : (C.X ∩ P.toFinset).card = C.w := by
    simpa [Finset.inter_comm] using hPX
  have hcard : (C.X \ P.toFinset).card = C.X.card - C.w := by
    rw [Finset.card_sdiff]
    exact congrArg (C.X.card - ·) hPX
  have hwX : C.w ≤ C.X.card := by
    rw [← hPX]
    exact Finset.card_le_card Finset.inter_subset_right
  have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, ← C.n_eq_c_sq_add_r]
  omega

private lemma claimOne_cover_of_path_and_remainder
    {P : List V} (hP : IsPath C.G P) (hPY : ∀ y ∈ C.Y, y ∈ P)
    {h : ℕ} (hD : HasPathCoverOnAtMost C.G (C.X \ P.toFinset : Set V) h) :
    HasPathCoverAtMost C.G (1 + h) := by
  have hPcover : HasPathCoverOnAtMost C.G (P.toFinset : Set V) 1 := by
    exact ⟨[P], by simp, by simpa using IsPathCoverOn.singleton_path hP⟩
  rw [hasPathCoverAtMost_iff_on_univ]
  have hcover := hPcover.append hD
  have hunion := C.claimOne_path_union_remainder hPY
  have hset : (P.toFinset : Set V) ∪ (C.X \ P.toFinset : Set V) = Set.univ := by
    ext v
    have hv := congrArg (fun S : Finset V ↦ v ∈ S) hunion
    simpa using hv
  rw [hset] at hcover
  exact hcover

private lemma claimOne_device_cases
    (hc : 4 ≤ C.c) (hmu : C.mu ≤ C.r - 2)
    (ht : C.c + 1 ≤ C.a0 + ceilHalf C.a1)
    {D : Finset V} (hDcard : D.card = C.c ^ 2 + C.r - 2 * C.w) :
    let h := C.c - 1
    coverDeviceP D C.Y0 h ≤ 0 ∨
      (0 < coverDeviceP D C.Y0 h ∧
        coverDeviceP D C.Y0 h ≤ (min h ((D.card - C.mu) / 2) : ℕ)) ∨
      (0 < coverDeviceP D C.Y0 h ∧
        coverDeviceP D C.Y0 h ≤
          (coverDeviceQ D C.Y0 h * C.Y1.card : ℕ) ∧
        coverDeviceP D C.Y0 h - (coverDeviceQ D C.Y0 h : ℕ) ≤
          (D.card : ℤ) - 2 * (C.mu : ℤ) ∧
        coverDeviceP D C.Y0 h + (coverDeviceQ D C.Y0 h : ℕ) ≤
          (D.card : ℤ) - (C.mu : ℤ)) := by
  dsimp only
  let h := C.c - 1
  let p := coverDeviceP D C.Y0 h
  have hh : 1 ≤ h := by
    change 1 ≤ C.c - 1
    omega
  have hh0 : 0 ≤ (h : ℤ) := by positivity
  have hr := C.r_le_two_mul_c
  have hw := C.w_le_r_sub_two
  have hw_add : C.w + 2 ≤ C.r := by
    have := C.w_ge_c
    omega
  have hmu_add : C.mu + 2 ≤ C.r := by
    have := C.w_ge_c
    omega
  have hwZ : (C.w : ℤ) ≤ (C.r : ℤ) - 2 := by
    have hwAddZ : (C.w : ℤ) + 2 ≤ (C.r : ℤ) := by exact_mod_cast hw_add
    omega
  have hmuZ : (C.mu : ℤ) ≤ (C.r : ℤ) - 2 := by
    have hmuAddZ : (C.mu : ℤ) + 2 ≤ (C.r : ℤ) := by exact_mod_cast hmu_add
    omega
  have ha0lo : 2 * C.c + 1 - C.w ≤ C.a0 :=
    claim1_a0_lower C.w_eq_a0_add_a1 ht
  have ha0three : 3 ≤ C.a0 :=
    claim1_a0_ge_three hc hw hr ha0lo
  have hdenseZ := claim1_dense_nonneg
    (c := (C.c : ℤ)) (r := (C.r : ℤ)) (w := (C.w : ℤ)) (μ := (C.mu : ℤ))
    (by exact_mod_cast hc) (by exact_mod_cast hr) hwZ hmuZ
  have htwowZ : 2 * (C.w : ℤ) ≤ (C.c : ℤ) ^ 2 + C.r := by
    have hmu0 : 0 ≤ (C.mu : ℤ) := by positivity
    nlinarith
  have htwow : 2 * C.w ≤ C.c ^ 2 + C.r := by exact_mod_cast htwowZ
  have hDcardZ : (D.card : ℤ) = (C.c : ℤ) ^ 2 + C.r - 2 * C.w := by
    rw [hDcard, Nat.cast_sub htwow]
    push_cast
    ring
  have hpdef : p = (D.card : ℤ) - (h * (C.a0 + 1) : ℕ) := by
    simp [p, coverDeviceP, h, Configuration.a0]
  by_cases hp0 : p ≤ 0
  · exact Or.inl hp0
  have hp : 0 < p := by omega
  by_cases hph : p ≤ (h : ℤ)
  · right; left
    refine ⟨hp, ?_⟩
    have hsmall := claim1_small_p_condition
      (c := (C.c : ℤ)) (r := (C.r : ℤ)) (w := (C.w : ℤ))
      (μ := (C.mu : ℤ)) (p := p)
      (by exact_mod_cast hc) (by exact_mod_cast hr) hwZ hmuZ
      (by
        have hhSucc : h + 1 = C.c := by
          dsimp [h]
          exact Nat.sub_add_cancel C.one_le_c
        have hhcast : (h : ℤ) = (C.c : ℤ) - 1 := by
          have hhSuccZ : (h : ℤ) + 1 = (C.c : ℤ) := by exact_mod_cast hhSucc
          omega
        omega)
    have htwo : 2 * p ≤ (D.card : ℤ) - C.mu := by
      rw [hDcardZ]
      exact hsmall
    have hpNat : (p.toNat : ℤ) = p := by omega
    have hmuD : C.mu ≤ D.card := by omega
    have htwoNat : p.toNat * 2 ≤ D.card - C.mu := by omega
    have hpDiv : p.toNat ≤ (D.card - C.mu) / 2 := by
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 htwoNat
    have hpH : p.toNat ≤ h := by omega
    have hpMin : p.toNat ≤ min h ((D.card - C.mu) / 2) :=
      ((Nat.le_min).2 ⟨hpH, hpDiv⟩)
    change p ≤ (min h ((D.card - C.mu) / 2) : ℕ)
    rw [← hpNat]
    exact_mod_cast hpMin
  · right; right
    have hh_lt_p : (h : ℤ) < p := by omega
    have hhSucc : h + 1 = C.c := by
      dsimp [h]
      exact Nat.sub_add_cancel C.one_le_c
    have hhcast : (h : ℤ) = (C.c : ℤ) - 1 := by
      have hhSuccZ : (h : ℤ) + 1 = (C.c : ℤ) := by exact_mod_cast hhSucc
      omega
    have hq : coverDeviceQ D C.Y0 h = h := by
      have hle : h ≤ p.toNat := by omega
      simp [coverDeviceQ, p, Nat.min_eq_right hle]
    refine ⟨hp, ?_, ?_, ?_⟩
    · have hwle : C.w ≤ 2 * C.c + 1 := by omega
      have ha0loZ : 2 * (C.c : ℤ) + 1 - (C.w : ℤ) ≤ (C.a0 : ℤ) := by
        calc
          2 * (C.c : ℤ) + 1 - (C.w : ℤ) =
              ((2 * C.c + 1 - C.w : ℕ) : ℤ) := by
                rw [Nat.cast_sub hwle]
                push_cast
                ring
          _ ≤ (C.a0 : ℤ) := by exact_mod_cast ha0lo
      have hwSuccZ := claim1_w_ge_succ
        (c := (C.c : ℤ)) (w := (C.w : ℤ)) (a0 := (C.a0 : ℤ))
        ha0loZ (by exact_mod_cast C.a0_le_w)
      have hdZ := claim1_d_le_sq_sub_two
        (c := (C.c : ℤ)) (r := (C.r : ℤ)) (w := (C.w : ℤ))
        (by exact_mod_cast hr) hwSuccZ
      have hdZ' : (D.card : ℤ) ≤ (C.c : ℤ) ^ 2 - 2 := by
        rw [hDcardZ]
        exact hdZ
      have hcap := claim1_large_p_capacity
        (c := (C.c : ℤ)) (d := (D.card : ℤ)) (h := (h : ℤ)) (w := (C.w : ℤ))
        (by omega) hhcast hwSuccZ hdZ'
      have hid := device_large_p_first_identity
        (d := (D.card : ℤ)) (h := (h : ℤ)) (p := p) (q := (h : ℤ))
        (a0 := (C.a0 : ℤ)) (a1 := (C.a1 : ℤ)) (w := (C.w : ℤ))
        (by simpa using hpdef) rfl (by exact_mod_cast C.w_eq_a0_add_a1)
      rw [hq]
      change p ≤ ((h * C.Y1.card : ℕ) : ℤ)
      have hpCapZ : p ≤ (h : ℤ) * (C.a1 : ℤ) := by omega
      simpa only [Nat.cast_mul, ← C.a1_eq_card_Y1] using hpCapZ
    · have hmu2h : (C.mu : ℤ) ≤ 2 * (h : ℤ) := by
        have hrZ : (C.r : ℤ) ≤ 2 * (C.c : ℤ) := by exact_mod_cast hr
        omega
      have hid := device_large_p_common_identity
        (d := (D.card : ℤ)) (μ := (C.mu : ℤ)) (p := p) (q := (h : ℤ))
        (h := (h : ℤ)) (a0 := (C.a0 : ℤ)) (by simpa using hpdef) rfl
      have ha0two : 2 ≤ C.a0 := by omega
      have ha0twoZ : (2 : ℤ) ≤ (C.a0 : ℤ) := by exact_mod_cast ha0two
      have hnonneg := claim1_large_p_common_nonneg
        (h := (h : ℤ)) (a0 := (C.a0 : ℤ)) (μ := (C.mu : ℤ))
        hh0 ha0twoZ hmu2h
      rw [hq]
      change p - (h : ℤ) ≤ (D.card : ℤ) - 2 * (C.mu : ℤ)
      omega
    · have hmu2h : (C.mu : ℤ) ≤ 2 * (h : ℤ) := by
        have hrZ : (C.r : ℤ) ≤ 2 * (C.c : ℤ) := by exact_mod_cast hr
        omega
      have hid := device_large_p_endpoint_identity
        (d := (D.card : ℤ)) (μ := (C.mu : ℤ)) (p := p) (q := (h : ℤ))
        (h := (h : ℤ)) (a0 := (C.a0 : ℤ)) (by simpa using hpdef) rfl
      have ha0two : 2 ≤ C.a0 := by omega
      have ha0twoZ : (2 : ℤ) ≤ (C.a0 : ℤ) := by exact_mod_cast ha0two
      have hnonneg := claim1_large_p_endpoint_nonneg
        (h := (h : ℤ)) (a0 := (C.a0 : ℤ)) (μ := (C.mu : ℤ))
        hh0 ha0twoZ hmu2h
      rw [hq]
      change p + (h : ℤ) ≤ (D.card : ℤ) - (C.mu : ℤ)
      omega

/-- If the parameter `t` of Chen--Chen Claim 1 were at least two, the dense
bipartite path and the covering device would give a forbidden `c`-path cover. -/
theorem claimOne_cover_of_large_t
    (hc : 4 ≤ C.c) (hmu : C.mu ≤ C.r - 2)
    (ht : C.c + 1 ≤ C.a0 + ceilHalf C.a1) :
    HasPathCoverAtMost C.G C.c := by
  classical
  obtain ⟨P, hP, _hPlen, _hPsub, hPY, hPX⟩ := C.claimOne_dense_path hmu hc
  let D : Finset V := C.X \ P.toFinset
  let h := C.c - 1
  have hDcard : D.card = C.c ^ 2 + C.r - 2 * C.w := by
    simpa [D] using C.claimOne_remainder_card hPX
  have hh : 1 ≤ h := by
    change 1 ≤ C.c - 1
    omega
  have hD : HasPathCoverOnAtMost C.G (D : Set V) h := by
    apply coverDevice (X := C.X) (Y₀ := C.Y0) (Y₁ := C.Y1) (D := D)
        (h := h) (mu := C.mu)
    · exact Finset.sdiff_subset
    · exact hh
    · exact C.X_disjoint_Y.mono_right C.Y0_subset_Y
    · exact C.X_disjoint_Y.mono_right C.Y1_subset_Y
    · exact C.Y0_disjoint_Y1
    · intro y hy x hx
      exact C.adj_of_mem_Y0_mem_X hy hx
    · exact C.claimOne_sparse_Y1
    · exact C.Y1_nonempty
    · simpa [h] using C.claimOne_device_cases hc hmu ht hDcard
  have hD' : HasPathCoverOnAtMost C.G (C.X \ P.toFinset : Set V) h := by
    simpa [D] using hD
  have hcover := C.claimOne_cover_of_path_and_remainder hP hPY hD'
  have hcount : 1 + h = C.c := by
    dsimp [h]
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel C.one_le_c
  rw [hcount] at hcover
  exact hcover

/-- **Chen--Chen Claim 1.**  For a normalized counterexample with `4 ≤ c`,
once the predecessor-clique bound `mu ≤ r - 2` is available, the parameter
`t = 1 + ceilHalf a1 + a0 - c` equals one.  Equivalently,
`a0 + ceilHalf a1 = c`. -/
theorem claim_one_of_mu_bound (hc : 4 ≤ C.c) (hmu : C.mu ≤ C.r - 2) :
    C.a0 + ceilHalf C.a1 = C.c := by
  apply le_antisymm
  · by_contra hle
    have ht : C.c + 1 ≤ C.a0 + ceilHalf C.a1 := by omega
    exact C.cover_failures.1 (C.claimOne_cover_of_large_t hc hmu ht)
  · have hfail := C.one_long_cover_failure
    omega

/-- Claim 1 with the predecessor-clique estimate discharged. -/
theorem claim_one (hc : 4 ≤ C.c) : C.a0 + ceilHalf C.a1 = C.c := by
  have hY0 : C.Y0.Nonempty := C.Y0_nonempty
  have hmu : C.mu ≤ C.r - 2 :=
    C.mu_le_r_sub_two_of_bounds C.Y1_nonempty hY0 (by omega) (by
      have := C.w_le_r_sub_two
      have := C.w_ge_c
      omega)
  exact C.claim_one_of_mu_bound hc hmu

end Configuration
end Erdos518
