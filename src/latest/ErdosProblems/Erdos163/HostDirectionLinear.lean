/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostSchedule

/-!
# A linear all-direction host lemma

This file instantiates the parameterized all-direction dependent-random-choice
theorem.  Every parameter except the scale is fixed, so the host and all of
its prepared parts grow linearly with the scale.
-/

open scoped BigOperators

namespace Erdos163
namespace HostDirectionLinear

theorem pow_mul_inv_pow_le_inv_pow (Z a b e : ℕ) (hZ : 1 ≤ Z)
    (h : a + b ≤ e) :
    (Z : ℝ) ^ a * ((Z : ℝ)⁻¹) ^ e ≤ ((Z : ℝ)⁻¹) ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_add]
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (Nat.zero_lt_one.trans_le hZ)
  have hne : (Z : ℝ) ^ a ≠ 0 := by positivity
  rw [inv_pow]
  calc
    (Z : ℝ) ^ a * (((Z : ℝ) ^ a)⁻¹ *
        ((Z : ℝ)⁻¹) ^ b * ((Z : ℝ)⁻¹) ^ c) =
        (Z : ℝ) ^ a * ((Z : ℝ) ^ a)⁻¹ *
          (((Z : ℝ)⁻¹) ^ b * ((Z : ℝ)⁻¹) ^ c) := by ring
    _ = ((Z : ℝ)⁻¹) ^ b * ((Z : ℝ)⁻¹) ^ c := by
      rw [mul_inv_cancel₀ hne, one_mul]
    _ ≤ ((Z : ℝ)⁻¹) ^ b := by
      have hc : ((Z : ℝ)⁻¹) ^ c ≤ 1 := by
        exact pow_le_one₀ (inv_pos.mpr hZpos).le
          ((inv_le_one₀ hZpos).2 (by exact_mod_cast hZ))
      exact mul_le_of_le_one_right (by positivity) hc

theorem scaled_pow_mul_inv_pow_le (K Z a b e : ℕ) (hZ : 1 ≤ Z)
    (hK : K ≤ Z ^ 4) (h : 4 * a + b ≤ e) :
    (K : ℝ) ^ a * ((Z : ℝ)⁻¹) ^ e ≤ ((Z : ℝ)⁻¹) ^ b := by
  have hKcast : (K : ℝ) ≤ (Z : ℝ) ^ 4 := by
    simpa [Nat.cast_pow] using
      (show (K : ℝ) ≤ (Z ^ 4 : ℕ) by exact_mod_cast hK)
  have hp : (K : ℝ) ^ a ≤ (Z : ℝ) ^ (4 * a) := by
    calc
      (K : ℝ) ^ a ≤ ((Z : ℝ) ^ 4) ^ a :=
        pow_le_pow_left₀ (by positivity) hKcast a
      _ = (Z : ℝ) ^ (4 * a) := by rw [← pow_mul]
  exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    (pow_mul_inv_pow_le_inv_pow Z (4 * a) b e hZ h)

theorem scaled_pow_mul_inv_pow_div_le
    (K Z a b e en : ℕ) (hZ : 1 ≤ Z) (hK : K ≤ Z ^ 4)
    (hen : en ≤ e) (h : 4 * a + b ≤ e - en) :
    (K : ℝ) ^ a * ((Z : ℝ)⁻¹) ^ e / ((Z : ℝ)⁻¹) ^ en ≤
      ((Z : ℝ)⁻¹) ^ b := by
  rw [show e = (e - en) + en by omega, pow_add]
  have hne : ((Z : ℝ)⁻¹) ^ en ≠ 0 := by positivity
  rw [show (K : ℝ) ^ a *
      (((Z : ℝ)⁻¹) ^ (e - en) * ((Z : ℝ)⁻¹) ^ en) =
      ((K : ℝ) ^ a * ((Z : ℝ)⁻¹) ^ (e - en)) *
        ((Z : ℝ)⁻¹) ^ en by ring,
    mul_div_cancel_right₀ _ hne]
  exact scaled_pow_mul_inv_pow_le K Z a b (e - en) hZ hK h

theorem two_mul_inv_pow_succ_le (Z e : ℕ) (hZ : 2 ≤ Z) :
    2 * ((Z : ℝ)⁻¹) ^ (e + 1) ≤ ((Z : ℝ)⁻¹) ^ e := by
  rw [pow_succ]
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  have htwo : (2 : ℝ) * (Z : ℝ)⁻¹ ≤ 1 := by
    rw [show (2 : ℝ) * (Z : ℝ)⁻¹ = 2 / Z by rw [div_eq_mul_inv]]
    exact (div_le_one hZpos).2 (by exact_mod_cast hZ)
  calc
    2 * (((Z : ℝ)⁻¹) ^ e * (Z : ℝ)⁻¹) =
        ((Z : ℝ)⁻¹) ^ e * (2 * (Z : ℝ)⁻¹) := by ring
    _ ≤ ((Z : ℝ)⁻¹) ^ e * 1 :=
      mul_le_mul_of_nonneg_left htwo (by positivity)
    _ = _ := by ring

/-- For fixed structural data and any requested reciprocal error scale, there
is a single linear host coefficient.  Every two-colouring of a complete host
of that order has a colour and `r` large parts satisfying all reverse
direction defect moments simultaneously. -/
theorem exists_all_directions_linear
    (r D s T zMin : ℕ) (hr : 2 ≤ r) (hD : 0 < D) (hT : 0 < T)
    (hzMin : 0 < zMin) :
    ∃ C : ℕ, ∃ ε : ℝ,
      0 < C ∧ T ≤ C ∧ 0 < ε ∧ ε ≤ (zMin : ℝ)⁻¹ ∧
      ε * (C : ℝ) ^ D ≤ (T : ℝ) ^ D * (zMin : ℝ)⁻¹ ∧
      ε * (C : ℝ) ^ (6 * D + 10) ≤ 1 ∧
      ∀ m : ℕ, 0 < m →
      ∀ (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = C * m →
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
        ∃ c : Bool, ∃ A : Fin r → Finset α,
          (∀ j, T * m ≤ (A j).card) ∧
          (∀ j, FiniteDefect.moment (HostNested.colorGraph G c) (T * m) s
            (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε) := by
  let S := HostSchedule.buildFrom D s (30 * D + 50) r
  let dim := D + S.widths.sum
  have hexps : S.exps.length = r + 1 := by
    simp [S]
  have he0lt : 0 < S.exps.length := by omega
  have herlt : r < S.exps.length := by omega
  let e0 := S.exps.get ⟨0, he0lt⟩
  let ef := S.exps.get ⟨r, herlt⟩
  let t0 := e0 + 1
  let F := HostNested.reserveFactor t0 ^ (2 * (r - 1))
  let Z := 8 * r + F + 4 ^ dim + zMin + T
  let K := F * Z ^ 2 * 4 ^ dim
  let C := K * T
  let ε : ℝ := ((Z : ℝ)⁻¹) ^ ef
  have hZ8 : 8 * r ≤ Z := by
    change 8 * r ≤ 8 * r + F + 4 ^ dim + zMin + T
    exact ((Nat.le_add_right (8 * r) F).trans
      (Nat.le_add_right (8 * r + F) (4 ^ dim))).trans
        ((Nat.le_add_right (8 * r + F + 4 ^ dim) zMin).trans
          (Nat.le_add_right (8 * r + F + 4 ^ dim + zMin) T))
  have hFZ : F ≤ Z := by
    change F ≤ 8 * r + F + 4 ^ dim + zMin + T
    exact ((Nat.le_add_left F (8 * r)).trans
      (Nat.le_add_right (8 * r + F) (4 ^ dim))).trans
        ((Nat.le_add_right (8 * r + F + 4 ^ dim) zMin).trans
          (Nat.le_add_right (8 * r + F + 4 ^ dim + zMin) T))
  have hfourZ : 4 ^ dim ≤ Z := by
    change 4 ^ dim ≤ 8 * r + F + 4 ^ dim + zMin + T
    omega
  have hzMinZ : zMin ≤ Z := by
    change zMin ≤ 8 * r + F + 4 ^ dim + zMin + T
    exact (Nat.le_add_left zMin (8 * r + F + 4 ^ dim)).trans
      (Nat.le_add_right (8 * r + F + 4 ^ dim + zMin) T)
  have hTZ : T ≤ Z := by
    change T ≤ 8 * r + F + 4 ^ dim + zMin + T
    exact Nat.le_add_left T (8 * r + F + 4 ^ dim + zMin)
  have hZpos : 0 < Z := by omega
  have hZone : 1 ≤ Z := hZpos
  have hZtwo : 2 ≤ Z := by omega
  have hFpos : 0 < F := by
    exact pow_pos (HostNested.reserveFactor_pos t0) _
  have hKpos : 0 < K := by
    exact Nat.mul_pos (Nat.mul_pos hFpos (pow_pos hZpos 2)) (pow_pos (by omega) dim)
  have hKZ : K ≤ Z ^ 4 := by
    dsimp [K]
    calc
      F * Z ^ 2 * 4 ^ dim ≤ Z * Z ^ 2 * Z := by gcongr
      _ = Z ^ 4 := by ring
  have hefpos : 0 < ef := by
    dsimp [ef]
    exact S.exp_pos r herlt
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεsmall : ε ≤ (zMin : ℝ)⁻¹ := by
    have hZposR : (0 : ℝ) < Z := by exact_mod_cast hZpos
    have hzMinposR : (0 : ℝ) < zMin := by exact_mod_cast hzMin
    have hbase : (Z : ℝ)⁻¹ ≤ (zMin : ℝ)⁻¹ := by
      exact inv_anti₀ hzMinposR (by exact_mod_cast hzMinZ)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hefpos)
    rw [show ε = ((Z : ℝ)⁻¹) ^ ef by rfl, hk, pow_succ]
    have hpow : ((Z : ℝ)⁻¹) ^ k ≤ 1 := by
      exact pow_le_one₀ (by positivity)
        ((inv_le_one₀ hZposR).2 (by exact_mod_cast hZone))
    exact (mul_le_of_le_one_left (by positivity) hpow).trans hbase
  have hefEq : ef = 30 * D + 51 := by
    dsimp [ef, S]
    simpa [Nat.add_assoc] using
      HostSchedule.buildFrom_final_exp D s (30 * D + 50) r
  have hεC : ε * (C : ℝ) ^ D ≤
      (T : ℝ) ^ D * (zMin : ℝ)⁻¹ := by
    have hscaled : (K : ℝ) ^ D * ((Z : ℝ)⁻¹) ^ ef ≤
        (Z : ℝ)⁻¹ := by
      simpa using scaled_pow_mul_inv_pow_le K Z D 1 ef hZone hKZ (by omega)
    have hnonneg : (0 : ℝ) ≤ (T : ℝ) ^ D := by positivity
    calc
      ε * (C : ℝ) ^ D =
          (T : ℝ) ^ D * ((K : ℝ) ^ D * ((Z : ℝ)⁻¹) ^ ef) := by
            dsimp [ε, C]
            push_cast
            rw [mul_pow]
            ring
      _ ≤ (T : ℝ) ^ D * (Z : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hscaled hnonneg
      _ ≤ (T : ℝ) ^ D * (zMin : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (by
          exact inv_anti₀ (by exact_mod_cast hzMin)
            (by exact_mod_cast hzMinZ)) hnonneg
  have hCZ : C ≤ Z ^ 5 := by
    dsimp [C]
    calc
      K * T ≤ Z ^ 4 * Z := Nat.mul_le_mul hKZ hTZ
      _ = Z ^ 5 := by ring
  have hstrong : ε * (C : ℝ) ^ (6 * D + 10) ≤ 1 := by
    let p := 6 * D + 10
    have hp : 5 * p ≤ ef := by dsimp [p]; omega
    have hCcast : (C : ℝ) ≤ (Z : ℝ) ^ 5 := by
      exact_mod_cast hCZ
    have hCpow : (C : ℝ) ^ p ≤ (Z : ℝ) ^ (5 * p) := by
      calc
        (C : ℝ) ^ p ≤ ((Z : ℝ) ^ 5) ^ p :=
          pow_le_pow_left₀ (by positivity) hCcast p
        _ = (Z : ℝ) ^ (5 * p) := by rw [← pow_mul]
    have hcancel := pow_mul_inv_pow_le_inv_pow Z (5 * p) 0 ef hZone (by omega)
    calc
      ε * (C : ℝ) ^ (6 * D + 10) ≤
          ((Z : ℝ)⁻¹) ^ ef * (Z : ℝ) ^ (5 * p) := by
            dsimp [ε, p]
            gcongr
      _ = (Z : ℝ) ^ (5 * p) * ((Z : ℝ)⁻¹) ^ ef := by ring
      _ ≤ ((Z : ℝ)⁻¹) ^ 0 := hcancel
      _ = 1 := by simp
  refine ⟨C, ε, Nat.mul_pos hKpos hT,
    (by dsimp [C]; exact Nat.le_mul_of_pos_left T hKpos), hεpos, hεsmall, hεC,
    hstrong, ?_⟩
  intro m hm α _ _ hcard G _
  let τ := T * m
  let L := Z * τ
  let reserve0 := Z * 4 ^ dim * L
  let err : ℕ → ℝ := fun q =>
    if hq : q < S.exps.length then ((Z : ℝ)⁻¹) ^ S.exps.get ⟨q, hq⟩
    else ε
  have hτpos : 0 < τ := Nat.mul_pos hT hm
  have hLpos : 0 < L := Nat.mul_pos hZpos hτpos
  have hreserve0pos : 0 < reserve0 :=
    Nat.mul_pos (Nat.mul_pos hZpos (pow_pos (by omega) dim)) hLpos
  have herr_get (q : ℕ) (hq : q < S.exps.length) :
      err q = ((Z : ℝ)⁻¹) ^ S.exps.get ⟨q, hq⟩ := by
    simp [err, hq]
  have herr_r : err r = ε := by
    rw [herr_get r herlt]
  have hCcard : F * reserve0 = C * m := by
    dsimp [reserve0, L, τ, C, K]
    ring
  have hglobalEq : K * τ = C * m := by
    dsimp [τ, C]
    ring
  have hdim : D + S.widths.sum = dim := rfl
  have hsmall : (r : ℝ) * (4 * ((Z : ℝ)⁻¹)) < 1 := by
    have hZposR : (0 : ℝ) < Z := by exact_mod_cast hZpos
    rw [show (r : ℝ) * (4 * (Z : ℝ)⁻¹) = (r * 4) / Z by
      rw [div_eq_mul_inv]; ring]
    apply (div_lt_one hZposR).2
    have hlt : 4 * r < Z := (by omega : 4 * r < 8 * r).trans_le hZ8
    exact_mod_cast (by simpa [mul_comm] using hlt)
  have hinv4le : ((Z : ℝ)⁻¹) ^ 4 ≤ (Z : ℝ)⁻¹ := by
    rw [show (4 : ℕ) = 1 + 3 by omega, pow_add, pow_one]
    have hZposR : (0 : ℝ) < Z := by exact_mod_cast hZpos
    have hp : ((Z : ℝ)⁻¹) ^ 3 ≤ 1 :=
      pow_le_one₀ (by positivity)
        ((inv_le_one₀ hZposR).2 (by exact_mod_cast hZone))
    exact mul_le_of_le_one_right (by positivity) hp
  have hnum : ∀ q, ∀ hq : q < S.widths.length,
      let w := S.widths.get ⟨q, hq⟩
      let dn := D + (S.widths.drop (q + 1)).sum
      (r : ℝ) *
        ((K : ℝ) ^ w * err q +
          (K : ℝ) ^ (dn + (dn + w)) * err q / err (q + 1) +
          ((K : ℝ) ^ (dn + (dn + w)) * err q / err (q + 1) +
            (K : ℝ) ^ dn * ((Z : ℝ)⁻¹) ^ w / err (q + 1))) < 1 := by
    intro q hq
    let w := S.widths.get ⟨q, hq⟩
    let dn := D + (S.widths.drop (q + 1)).sum
    have hwidthLen : S.widths.length = r := by simp [S]
    have hqr : q < r := by simpa [hwidthLen] using hq
    have hqexp : q < S.exps.length := by rw [hexps]; omega
    have hq1exp : q + 1 < S.exps.length := by rw [hexps]; omega
    let e := S.exps.get ⟨q, hqexp⟩
    let en := S.exps.get ⟨q + 1, hq1exp⟩
    have hb := S.bounds q hq
    change 4 * w + 4 ≤ e ∧
        4 * (dn + (dn + w)) + 4 ≤ e - en ∧
        4 * dn + en + 4 ≤ w at hb
    have heren : err q = ((Z : ℝ)⁻¹) ^ e := by
      simpa [e] using herr_get q hqexp
    have heren1 : err (q + 1) = ((Z : ℝ)⁻¹) ^ en := by
      simpa [en] using herr_get (q + 1) hq1exp
    have henen : en ≤ e := by omega
    have hwen : en ≤ w := by omega
    have h1 : (K : ℝ) ^ w * err q ≤ ((Z : ℝ)⁻¹) ^ 4 := by
      rw [heren]
      exact scaled_pow_mul_inv_pow_le K Z w 4 e hZone hKZ hb.1
    have h2 : (K : ℝ) ^ (dn + (dn + w)) * err q / err (q + 1) ≤
        ((Z : ℝ)⁻¹) ^ 4 := by
      rw [heren, heren1]
      exact scaled_pow_mul_inv_pow_div_le K Z (dn + (dn + w)) 4 e en
        hZone hKZ henen hb.2.1
    have h3 : (K : ℝ) ^ dn * ((Z : ℝ)⁻¹) ^ w / err (q + 1) ≤
        ((Z : ℝ)⁻¹) ^ 4 := by
      rw [heren1]
      apply scaled_pow_mul_inv_pow_div_le K Z dn 4 w en hZone hKZ hwen
      omega
    calc
      (r : ℝ) *
          ((K : ℝ) ^ w * err q +
            (K : ℝ) ^ (dn + (dn + w)) * err q / err (q + 1) +
            ((K : ℝ) ^ (dn + (dn + w)) * err q / err (q + 1) +
              (K : ℝ) ^ dn * ((Z : ℝ)⁻¹) ^ w / err (q + 1))) ≤
          (r : ℝ) * (4 * ((Z : ℝ)⁻¹) ^ 4) := by
            gcongr
            linarith
      _ ≤ (r : ℝ) * (4 * (Z : ℝ)⁻¹) := by gcongr
      _ < 1 := hsmall
  have herrpos : ∀ q, q ≤ S.widths.length → 0 < err q := by
    intro q hq
    have hqexp : q < S.exps.length := by
      rw [S.length_exps]
      omega
    rw [herr_get q hqexp]
    positivity
  obtain ⟨c, A, hAcard, hAmoment⟩ :=
    HostDirections.exists_all_directions_of_list_parameters G
      (r := r) (D := D) (s := s) (t₀ := t0) (L := L)
      (reserve₀ := reserve0) (τ := τ) (K := K)
      (η := (Z : ℝ)⁻¹) (η₀ := (Z : ℝ)⁻¹) S.widths err
      (hr := hr) (hlen := by simp [S]) (hD := hD)
      (hwidth := fun w hw =>
        HostSchedule.buildFrom_width_mem D s (30 * D + 50) r hw)
      (ht₀ := by dsimp [t0]; omega) (hL := hLpos)
      (hLreserve := by
        dsimp [reserve0]
        exact Nat.le_mul_of_pos_left L
          (Nat.mul_pos hZpos (pow_pos (by omega) dim)))
      (hτ := hτpos) (hτL := by dsimp [L]; exact Nat.le_mul_of_pos_left τ hZpos)
      (hK := hKpos) (hη := by positivity) (hηL := by
        dsimp [L, τ]
        have hZneR : (Z : ℝ) ≠ 0 := by positivity
        norm_num [Nat.cast_mul]
        field_simp
        norm_num)
      (hη₀ := by positivity)
      (hnestedThreshold := by
        dsimp [reserve0, L]
        rw [hdim]
        have hZneR : (Z : ℝ) ≠ 0 := by positivity
        have h4ne : (4 : ℝ) ^ dim ≠ 0 := by positivity
        norm_num [Nat.cast_mul, Nat.cast_pow]
        field_simp
        rw [← mul_pow]
        norm_num)
      (hnestedCard := by
        rw [hcard]
        simpa [F] using hCcard.le)
      (hglobal := by rw [hcard, hglobalEq])
      (herr0 := by
        have he0 : err 0 = ((Z : ℝ)⁻¹) ^ e0 := by
          simpa [e0] using herr_get 0 he0lt
        rw [he0]
        exact two_mul_inv_pow_succ_le Z e0 hZtwo)
      (herrpos := herrpos)
      (hnum := hnum)
  refine ⟨c, A, ?_, ?_⟩
  · simpa [τ] using hAcard
  · intro j
    simpa [τ, herr_r] using hAmoment j

end HostDirectionLinear
end Erdos163
