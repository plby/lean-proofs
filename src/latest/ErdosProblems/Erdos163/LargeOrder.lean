/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostDirectionLinear
import ErdosProblems.Erdos163.FailureEstimate
import ErdosProblems.Erdos163.Conclusion

/-!
# The large-order Burr--Erdős theorem

This is the final quantitative assembly.  The eighth-root scale converts all
fractional powers in Lee's argument to natural powers.  The only use of
limits is the elementary fact that a fixed polynomial times `exp (-c a)`
tends to zero.
-/

open scoped BigOperators
open Finset

namespace Erdos163

noncomputable section

structure HostNumericalPackage (r D Q L T : ℕ) where
  C : ℕ
  ε : ℝ
  hC : 0 < C
  hTC : 2 * T ≤ C
  hε : 0 < ε
  hεsmall : ε ≤ (1 : ℝ)⁻¹
  hεC : ε * (C : ℝ) ^ D ≤ ((2 * T : ℕ) : ℝ) ^ D * (1 : ℝ)⁻¹
  hstrong : ε * (C : ℝ) ^ (6 * D + 10) ≤ 1
  hhost : ∀ (m : ℕ), 0 < m →
    ∀ (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = C * m →
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
        ∃ c A,
          (∀ j : Fin r, 2 * T * m ≤ (A j).card) ∧
          ∀ j : Fin r, FiniteDefect.moment (HostNested.colorGraph G c)
            (2 * T * m) (4 * D) (fun _ : Fin D => HostDirections.unionExcept A j)
              (A j) ≤ ε
  hC1 : 1 ≤ C
  hCtwo : 2 ≤ C
  hLC : L ≤ C
  hQC : Q ≤ C
  hDC : D ≤ C
  h256C : 256 ≤ C
  hγ : (1 : ℝ) ≤ 16 * (C + 1)
  hBcoef : 0 < 2 * RandomGreedy.branchCoefficient (2 * (16 * (C + 1))) D
  hμ : 0 < 1 / (64 * Q * L *
    (2 * RandomGreedy.branchCoefficient (2 * (16 * (C + 1))) D))
  hBbound : 2 * RandomGreedy.branchCoefficient (2 * (16 * (C + 1))) D ≤
    (C : ℝ) ^ (4 * D + 3)
  hdenBound : (256 : ℝ) * Q * L *
    (2 * RandomGreedy.branchCoefficient (2 * (16 * (C + 1))) D) ≤
      (C : ℝ) ^ (4 * D + 6)
  hmainSmall : 4 * ε * (C : ℝ) ^ D ≤
    1 / (64 * Q * L *
      (2 * RandomGreedy.branchCoefficient (2 * (16 * (C + 1))) D))

theorem exists_hostNumericalPackage (d : ℕ) (hd : 1 ≤ d) :
    Nonempty (HostNumericalPackage (d + 1) (4 * d)
      (8 * (d + 1) * (16 * (4 * d))) (16 * (4 * d))
      (8 * (8 * (d + 1) * (16 * (4 * d))))) := by
  let D := 4 * d
  let r := d + 1
  let L := 16 * D
  let Q := 8 * r * L
  let T := 8 * Q
  have hD : 0 < D := by dsimp [D]; omega
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨C, ε, hC, hTC, hε, hεsmall, hεC, hstrong, hhost⟩ :=
    HostDirectionLinear.exists_all_directions_linear
      r D (4 * D) (2 * T) 1 hr hD (by positivity) (by omega)
  let γ : ℝ := 16 * (C + 1)
  let Bcoef : ℝ := 2 * RandomGreedy.branchCoefficient (2 * γ) D
  let μ : ℝ := 1 / (64 * Q * L * Bcoef)
  have hC1 : 1 ≤ C := hC
  have hCtwo : 2 ≤ C := by
    have hQT : 2 ≤ 2 * T := by omega
    exact hQT.trans hTC
  have hLC : L ≤ C := by
    exact (by dsimp [T, Q]; nlinarith : L ≤ 2 * T).trans hTC
  have hQC : Q ≤ C := by
    exact (by dsimp [T]; omega : Q ≤ 2 * T).trans hTC
  have hDC : D ≤ C := by
    exact (by dsimp [L]; omega : D ≤ L).trans hLC
  have h256C : 256 ≤ C := by
    have : 256 ≤ 2 * T := by
      dsimp [T, Q, r, L, D]
      nlinarith
    exact this.trans hTC
  have hγ : 1 ≤ γ := by
    dsimp [γ]
    have : (0 : ℝ) ≤ C := by positivity
    nlinarith
  have hBcoef : 0 < Bcoef := by
    dsimp [Bcoef, RandomGreedy.branchCoefficient]
    positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hBbound : Bcoef ≤ (C : ℝ) ^ (4 * D + 3) := by
    have h2γ : 2 * γ ≤ (C : ℝ) ^ 2 := by
      dsimp [γ]
      have h64 : (64 : ℝ) ≤ C := by exact_mod_cast h256C.trans' (by omega)
      have hC0 : (0 : ℝ) ≤ C := by positivity
      nlinarith
    have hpow : (2 * γ) ^ D ≤ (C : ℝ) ^ (2 * D) := by
      calc
        (2 * γ) ^ D ≤ ((C : ℝ) ^ 2) ^ D :=
          pow_le_pow_left₀ (by positivity) h2γ D
        _ = (C : ℝ) ^ (2 * D) := by rw [← pow_mul]
    have hmul : (D : ℝ) * (2 * γ) ^ D ≤ (C : ℝ) ^ (2 * D + 1) := by
      calc
        (D : ℝ) * (2 * γ) ^ D ≤ C * C ^ (2 * D) := by
          exact mul_le_mul (by exact_mod_cast hDC) hpow (by positivity) (by positivity)
        _ = (C : ℝ) ^ (2 * D + 1) := by rw [pow_succ]; ring
    have hsq : ((D : ℝ) * (2 * γ) ^ D) ^ 2 ≤
        (C : ℝ) ^ (4 * D + 2) := by
      calc
        ((D : ℝ) * (2 * γ) ^ D) ^ 2 ≤
            ((C : ℝ) ^ (2 * D + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hmul 2
        _ = (C : ℝ) ^ (4 * D + 2) := by rw [← pow_mul]; congr 1; omega
    have hBeq : Bcoef = ((D : ℝ) * (2 * γ) ^ D) ^ 2 + 1 := by
      dsimp [Bcoef, RandomGreedy.branchCoefficient]
      ring
    have hpowOne : (1 : ℝ) ≤ C ^ (4 * D + 2) := one_le_pow₀ (by exact_mod_cast hC1)
    rw [hBeq]
    calc
      ((D : ℝ) * (2 * γ) ^ D) ^ 2 + 1 ≤
          2 * C ^ (4 * D + 2) := by linarith
      _ ≤ C * C ^ (4 * D + 2) := by gcongr; exact_mod_cast hCtwo
      _ = C ^ (4 * D + 3) := by rw [pow_succ]; ring
  have hdenBound : (256 : ℝ) * Q * L * Bcoef ≤
      (C : ℝ) ^ (4 * D + 6) := by
    calc
      (256 : ℝ) * Q * L * Bcoef ≤
          C * C * C * C ^ (4 * D + 3) := by
        gcongr <;> exact_mod_cast (show 256 ≤ C from h256C)
      _ = C ^ (4 * D + 6) := by
        rw [show 4 * D + 6 = (4 * D + 3) + 3 by omega, pow_add]
        ring
  have hmainSmall : 4 * ε * (C : ℝ) ^ D ≤ μ := by
    have hCpowMono : (C : ℝ) ^ (5 * D + 6) ≤ C ^ (6 * D + 10) :=
      pow_le_pow_right₀ (by exact_mod_cast hC1) (by omega)
    have hprod : 4 * ε * C ^ D * (64 * Q * L * Bcoef) ≤ 1 := by
      calc
        4 * ε * C ^ D * (64 * Q * L * Bcoef) =
            ε * C ^ D * (256 * Q * L * Bcoef) := by ring
        _ ≤ ε * C ^ D * C ^ (4 * D + 6) := by gcongr
        _ = ε * C ^ (5 * D + 6) := by
          rw [show 5 * D + 6 = D + (4 * D + 6) by omega, pow_add]
          ring
        _ ≤ ε * C ^ (6 * D + 10) := by gcongr
        _ ≤ 1 := hstrong
    dsimp [μ]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Q * L * Bcoef)).2
      (by simpa [mul_assoc] using hprod)
  change Nonempty (HostNumericalPackage r D Q L T)
  have hεsmall' : ε ≤ (1 : ℝ)⁻¹ := by
    simpa only [Nat.cast_one] using hεsmall
  have hεC' : ε * (C : ℝ) ^ D ≤
      ((2 * T : ℕ) : ℝ) ^ D * (1 : ℝ)⁻¹ := by
    simpa only [Nat.cast_one] using hεC
  exact ⟨⟨C, ε, hC, hTC, hε, hεsmall', hεC', hstrong, hhost,
    hC1, hCtwo, hLC, hQC, hDC, h256C, hγ, hBcoef, hμ, hBbound,
    hdenBound, hmainSmall⟩⟩

theorem largeOrderDegenerateRamsey : LargeOrderDegenerateRamsey := by
  intro d hd
  let D := 4 * d
  let r := d + 1
  let L := 16 * D
  let Q := 8 * r * L
  let T := 8 * Q
  have hD : 0 < D := by dsimp [D]; omega
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hL16 : 16 * D ≤ L := by rfl
  have hL : 2 ≤ L := by dsimp [L, D]; omega
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  let hp := (exists_hostNumericalPackage d hd).some
  change HostNumericalPackage r D Q L T at hp
  rcases hp with ⟨C, ε, hC, hTC, hε, hεsmall, hεC, hstrong, hhost,
    hC1, hCtwo, hLC, hQC, hDC, h256C, hγ, hBcoef, hμ, hBbound,
    hdenBound, hmainSmall⟩
  let γ : ℝ := 16 * (C + 1)
  let Bcoef : ℝ := 2 * RandomGreedy.branchCoefficient (2 * γ) D
  let μ : ℝ := 1 / (64 * Q * L * Bcoef)
  let Rcoef := (D + 1) * r
  let lam := D * C ^ D + 1
  let c₁ : ℝ := 1 / (4 * Q ^ 2)
  let c₃ : ℝ := μ ^ 2 / (2 * C * Q ^ (2 * D) * (lam ^ 2 + 1))
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₃ : 0 < c₃ := by dsimp [c₃]; positivity
  let polyK : ℝ := 2 * r + C ^ D
  obtain ⟨a₁, ha₁⟩ := FinalTools.eventually_const_mul_pow_mul_exp_neg_lt
    polyK (8 * D + 8) (by dsimp [polyK]; positivity) hc₁ (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨a₂, ha₂⟩ := FinalTools.eventually_const_mul_pow_mul_exp_neg_lt
    (2 * r) (8 * D + 8) (by positivity) hc₁ (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨a₃, ha₃⟩ := FinalTools.eventually_const_mul_pow_mul_exp_neg_lt
    1 (8 * D + 8) (by norm_num) hc₃ (by norm_num : (0 : ℝ) < 1 / 3)
  let diagK : ℝ :=
    16 * D ^ 4 * C ^ (2 * D) * Q ^ (2 * D) * 2 ^ (2 * D) / μ ^ 2
  let a₄ := Nat.ceil diagK + 1
  let abase := max (2 * Rcoef + 1) (max C (max lam a₄))
  let a₀ := max abase (max a₁ (max a₂ a₃))
  let n₀ := a₀ ^ 8 + 1
  refine ⟨256 * C, n₀, by omega, ?_⟩
  intro n hn H hdeg
  have hnpos : 0 < n := by dsimp [n₀] at hn; omega
  let a := FinalTools.scale n
  have ha : a₀ ≤ a := by
    have hpow : a₀ ^ 8 < n := by dsimp [n₀] at hn; omega
    exact (FinalTools.scale_ge_of_pow_lt hpow).le
  have habase : abase ≤ a := (le_max_left _ _).trans ha
  have ha₁' : a₁ ≤ a := (le_max_left _ _).trans (le_max_right _ _ |>.trans ha)
  have ha₂' : a₂ ≤ a :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _ |>.trans ha))
  have ha₃' : a₃ ≤ a :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _ |>.trans ha))
  have hRcoefA : 2 * Rcoef < a := by
    have := (le_max_left (2 * Rcoef + 1) (max C (max lam a₄))).trans habase
    omega
  have hCa : C ≤ a :=
    (le_max_left C (max lam a₄)).trans
      ((le_max_right (2 * Rcoef + 1) _).trans habase)
  have hlama : lam ≤ a :=
    (le_max_left lam a₄).trans ((le_max_right C _).trans
      ((le_max_right (2 * Rcoef + 1) _).trans habase))
  have ha₄a : a₄ ≤ a :=
    (le_max_right lam a₄).trans ((le_max_right C _).trans
      ((le_max_right (2 * Rcoef + 1) _).trans habase))
  have hapos : 0 < a := FinalTools.scale_pos n
  have hnA : n ≤ a ^ 8 := FinalTools.le_scale_pow n
  have hAlinear : a ^ 8 ≤ 256 * n := FinalTools.scale_pow_le hnpos
  let N := C * a ^ 8
  let oldθ := 2 * T * a ^ 8
  let τ := T * a ^ 8
  have hmpos : 0 < a ^ 8 := pow_pos hapos 8
  let f : Fin N ↪ Fin (256 * C * n) :=
    Fin.castLEEmb (by dsimp [N]; nlinarith [Nat.mul_le_mul_left C hAlinear])
  intro Gbig
  let : DecidableRel Gbig.Adj := Classical.decRel _
  let G : SimpleGraph (Fin N) := Gbig.comap f
  let : DecidableRel G.Adj := fun x y => inferInstance
  have hNcard : Fintype.card (Fin N) = C * a ^ 8 := by simp [N]
  obtain ⟨hostColor, A, hAcard, hAmoment⟩ :=
    hhost (a ^ 8) hmpos (Fin N) hNcard G
  have hAcard' : ∀ j, oldθ ≤ (A j).card := by simpa [oldθ] using hAcard
  have hAmoment' : ∀ j, FiniteDefect.moment
      (HostNested.colorGraph G hostColor) oldθ (4 * D)
      (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε := by
    simpa [oldθ] using hAmoment
  let Gc := HostNested.colorGraph G hostColor
  let : DecidableRel Gc.Adj := HostNested.colorGraph_decidableAdj G hostColor
  -- The remaining hypotheses are target-dependent but all numerical bounds
  -- are uniform in `H` and `n`.
  classical
  let layer : Fin n → Fin (n + 1) := fun x =>
    ⟨Decomposition.layerIndex H d x, by
      have hx := Decomposition.layerIndex_le_card H hd hdeg x
      simpa using Nat.lt_succ_of_le hx⟩
  have hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x := fun _ => rfl
  let col : H.Coloring (Fin (d + 1)) := (colorable_succ H d hdeg).some
  let c : Fin n → Fin (d + 1) := col
  have hcproper : ∀ x y, H.Adj x y → c x ≠ c y := by
    intro x y hxy
    exact col.map_rel hxy
  let P := TargetParts.OccupiedPart layer c
  let part : Fin n → P := TargetParts.part layer c
  let color : P → Fin r := fun p => ⟨(TargetParts.colorOf p).1, by simpa [r] using (TargetParts.colorOf p).2⟩
  let q : P → ℝ := TargetWeights.mass L Q
  let threshold : P → ℕ := TargetWeights.threshold L Q τ
  let := TargetParts.vertexOrder layer c
  let R₀ := a ^ 5
  let R := Rcoef * R₀
  let M := a ^ 6
  let Λ : ℕ → ℝ := fun k => if k = 0 then (a : ℝ)⁻¹ ^ 8
    else (lam : ℝ) * a ^ (8 * k - 5)
  let meanBound : Fin n → ℝ := fun x =>
    let k := Fintype.card (RandomGreedy.forwardNeighbors H x)
    (∏ y : RandomGreedy.forwardNeighbors H x, q (part y)) *
        ((N : ℝ) ^ k * ε) +
      (k : ℝ) ^ 2 * ((N : ℝ) ^ (k - 1) * ε)
  let tail : Fin n → ℝ := fun x =>
    μ / 2 * ∏ y : RandomGreedy.forwardNeighbors H x,
      (q (part y) * (τ : ℝ) / 2)
  let sizeTail : P → ℝ := fun p => q p * N
  have hbad : (PrunedHost.allBadLevels (D := D) (θ := oldθ)
      (s := 4 * D) Gc A Λ).card ≤ R := by
    have hb0 : (PrunedHost.allBadLevels (D := D) (θ := oldθ)
        (s := 4 * D) Gc A Λ).card ≤ (D + 1) * r * R₀ := by
      apply PrunedHost.allBadLevels_card_le Gc A Λ
      · intro j
        by_cases hj : j.1 = 0
        · let k : Fin r := ⟨1, hr⟩
          exact (Finset.card_pos.mp ((by positivity : 0 < oldθ).trans_le (hAcard' k))).mono
            (HostDirections.subset_unionExcept A (by intro h; simpa [k, hj] using congrArg Fin.val h))
        · let k : Fin r := ⟨0, by omega⟩
          exact (Finset.card_pos.mp ((by positivity : 0 < oldθ).trans_le (hAcard' k))).mono
            (HostDirections.subset_unionExcept A (by intro h; apply hj; exact (congrArg Fin.val h).symm))
      · exact hε.le
      · intro k hk
        dsimp [Λ]
        split_ifs <;> positivity
      · exact hAmoment'
      · intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp only [CharP.cast_eq_zero, pow_zero, one_mul, zero_mul, Nat.cast_add, Nat.cast_one]
          positivity
        · rw [show Λ k = (lam : ℝ) * a ^ (8 * k - 5) by simp [Λ, hk0]]
          have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hkD : k ≤ D := hk
          have hCk : C ^ k ≤ C ^ D := Nat.pow_le_pow_right hC1 hkD
          have hcoeff : (k : ℝ) * (C : ℝ) ^ k * ε < lam := by
            have hεone : ε ≤ 1 := hεsmall.trans (by norm_num)
            have hnat : k * C ^ k ≤ D * C ^ D := Nat.mul_le_mul hkD hCk
            have hlt : (k : ℝ) * C ^ k * ε < D * C ^ D + 1 := by
              calc
                (k : ℝ) * C ^ k * ε ≤ k * C ^ k * 1 := by gcongr
                _ ≤ D * C ^ D := by simpa using (by exact_mod_cast hnat :
                  (k : ℝ) * C ^ k ≤ D * C ^ D)
                _ < D * C ^ D + 1 := by linarith
            simpa [lam] using hlt
          dsimp [N, R₀]
          push_cast
          have hsplit : (a : ℝ) ^ (8 * k) = a ^ 5 * a ^ (8 * k - 5) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            (k : ℝ) * (((C : ℝ) * a ^ 8) ^ k * ε) =
                ((k : ℝ) * C ^ k * ε) * a ^ (8 * k) := by
              rw [mul_pow, ← pow_mul]
              ring
            _ < (lam : ℝ) * a ^ (8 * k) :=
              mul_lt_mul_of_pos_right hcoeff (by positivity)
            _ = (lam : ℝ) * (a ^ 5 * a ^ (8 * k - 5)) := by rw [hsplit]
            _ ≤ (a ^ 5 + 1) * ((lam : ℝ) * a ^ (8 * k - 5)) := by
              have hz : (0 : ℝ) ≤ (lam : ℝ) * a ^ (8 * k - 5) := by positivity
              nlinarith
    simpa [R, Rcoef, R₀, Nat.mul_assoc] using hb0
  have holdθ : 0 < oldθ := by dsimp [oldθ]; positivity
  have hτpos : 0 < τ := by dsimp [τ]; positivity
  have hτold : (τ : ℝ) ≤ (oldθ : ℝ) / 2 := by
    dsimp [τ, oldθ]
    push_cast
    ring_nf
    exact le_rfl
  have hRleτ : R ≤ τ := by
    have hRa : Rcoef ≤ a := by omega
    calc
      R = Rcoef * a ^ 5 := by rfl
      _ ≤ a * a ^ 5 := Nat.mul_le_mul_right _ hRa
      _ = a ^ 6 := by ring
      _ ≤ T * a ^ 8 := by
        have ha1 : 1 ≤ a := hapos
        have hp : a ^ 6 ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by omega)
        exact hp.trans (Nat.le_mul_of_pos_left _ hT)
      _ = τ := rfl
  have hτR : τ + R ≤ oldθ := by
    have : τ + R ≤ τ + τ := Nat.add_le_add_left hRleτ τ
    calc
      τ + R ≤ τ + τ := this
      _ = oldθ := by simp [τ, oldθ, two_mul, Nat.mul_assoc]
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMold : M < oldθ := by
    have ha1 : 1 ≤ a := hapos
    have hp : a ^ 6 ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by omega)
    have hfac : 1 < 2 * T := by omega
    have hstrict : a ^ 8 < (2 * T) * a ^ 8 := by
      simpa using Nat.mul_lt_mul_of_pos_right hfac hmpos
    have hpM : M ≤ a ^ 8 := by simpa [M] using hp
    have hstrictOld : a ^ 8 < oldθ := by simpa [oldθ] using hstrict
    exact hpM.trans_lt hstrictOld
  have hRM : 2 * R < M := by
    dsimp [R, Rcoef, R₀, M]
    calc
      2 * (Rcoef * a ^ 5) = (2 * Rcoef) * a ^ 5 := by ring
      _ < a * a ^ 5 := Nat.mul_lt_mul_of_pos_right hRcoefA (pow_pos hapos 5)
      _ = a ^ 6 := by ring
  have hNpos : 1 ≤ N := by
    have : 0 < N := by dsimp [N]; exact Nat.mul_pos hC hmpos
    omega
  have hcommonNumeric : (N : ℝ) ^ D * ε <
      ((oldθ : ℝ) / M) ^ (4 * D) := by
    have hbase : ((2 * T : ℕ) : ℝ) ^ D < ((2 * T : ℕ) : ℝ) ^ (4 * D) := by
      apply pow_lt_pow_right₀ (by exact_mod_cast (show 1 < 2 * T by omega))
      omega
    have ha8D : (0 : ℝ) < (a : ℝ) ^ (8 * D) := by positivity
    have hlhs : (N : ℝ) ^ D * ε ≤
        ((2 * T : ℕ) : ℝ) ^ D * a ^ (8 * D) := by
      calc
        (N : ℝ) ^ D * ε = (ε * C ^ D) * a ^ (8 * D) := by
          dsimp [N]
          push_cast
          rw [mul_pow, ← pow_mul]
          ring
        _ ≤ ((2 * T : ℕ) : ℝ) ^ D * a ^ (8 * D) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa only [Nat.cast_one, inv_one, mul_one] using hεC
    have hstrict : ((2 * T : ℕ) : ℝ) ^ D * a ^ (8 * D) <
        ((2 * T : ℕ) : ℝ) ^ (4 * D) * a ^ (8 * D) :=
      mul_lt_mul_of_pos_right hbase ha8D
    calc
      (N : ℝ) ^ D * ε ≤ _ := hlhs
      _ < ((2 * T : ℕ) : ℝ) ^ (4 * D) * a ^ (8 * D) := hstrict
      _ = ((oldθ : ℝ) / M) ^ (4 * D) := by
        dsimp [oldθ, M]
        push_cast
        have haR : (a : ℝ) ≠ 0 := by positivity
        have hratio : (2 * (T : ℝ) * a ^ 8) / a ^ 6 =
            2 * T * a ^ 2 := by
          field_simp
        rw [hratio]
        calc
          (2 * (T : ℝ)) ^ (4 * D) * a ^ (8 * D) =
              (2 * T) ^ (4 * D) * (a ^ 2) ^ (4 * D) := by
            congr 1
            rw [← pow_mul]
            congr 1
            omega
          _ = ((2 * T) * a ^ 2) ^ (4 * D) :=
            (mul_pow (2 * (T : ℝ)) (a ^ 2) (4 * D)).symm
  have hpart : ∀ x y, H.Adj x y → part x ≠ part y := by
    intro x y hxy
    exact TargetParts.part_ne_of_color_ne layer c (hcproper x y hxy)
  have horder : ∀ x y, H.Adj x y →
      (@LT.lt (Fin n) (TargetParts.vertexOrder layer c).toLT x y ↔
        part x < part y) := by
    intro x y hxy
    simpa [part] using TargetParts.vertex_lt_iff_part_lt_of_ne layer c
      (TargetParts.part_ne_of_color_ne layer c (hcproper x y hxy))
  have hcolor : ∀ x y, H.Adj x y → color (part x) ≠ color (part y) := by
    intro x y hxy heq
    have hv := congrArg Fin.val heq
    apply hcproper x y hxy
    apply Fin.ext
    simpa [color, part, c] using hv
  have hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D := by
    intro x
    simpa [D] using TargetParts.forwardNeighbors_card_le
      H hd hdeg layer c hcproper hlayer x
  have hτlarge : 8 * Q * n ≤ τ := by
    change 8 * Q * n ≤ 8 * Q * a ^ 8
    exact Nat.mul_le_mul_left (8 * Q) hnA
  have hthreshold : ∀ p, 0 < threshold p := by
    intro p
    exact TargetWeights.threshold_pos H hd hdeg layer c hlayer
      (by omega : 0 < L) hQ hτlarge p
  have hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x) := by
    intro x
    exact TargetWeights.twice_partVertices_le_threshold H hd hdeg layer c hlayer
      (by omega : 0 < L) hQ hτlarge x
  have hqpos : ∀ p, 0 < q p := fun p => TargetWeights.mass_pos hQ p
  have hqsum : ∑ p, q p ≤ 1 := by
    have hs := TargetWeights.sum_mass_le (by omega : 0 < L) layer c (Q := Q)
    have hnat : (d + 1) * (2 * L) ≤ 8 * (d + 1) * L := by
      calc
        (d + 1) * (2 * L) = 2 * ((d + 1) * L) := by ring
        _ ≤ 8 * ((d + 1) * L) := Nat.mul_le_mul_right _ (by omega)
        _ = 8 * (d + 1) * L := by ring
    calc
      ∑ p, q p ≤ ((d + 1 : ℕ) : ℝ) * (2 * L : ℕ) / Q := hs
      _ ≤ 1 := by
        have hden : (0 : ℝ) < Q := by positivity
        apply (div_le_one hden).2
        dsimp [Q, r]
        exact_mod_cast hnat
  have hthresholdSample : ∀ p, (threshold p : ℝ) ≤ q p * τ / 2 := by
    intro p
    calc
      (threshold p : ℝ) ≤ q p * τ / 4 :=
        TargetWeights.threshold_le_mass_mul layer c p
      _ ≤ q p * τ / 2 := by
        have hprod : 0 ≤ q p * (τ : ℝ) := mul_nonneg (hqpos p).le (by positivity)
        linarith
  have hΛpos : ∀ k, k ≤ D → 0 < Λ k := by
    intro k hk
    dsimp [Λ]
    split_ifs <;> positivity
  have hmeanNumeric : ∀ x,
      (∏ y : RandomGreedy.forwardNeighbors H x, q (part y)) *
          ((N : ℝ) ^ Fintype.card (RandomGreedy.forwardNeighbors H x) * ε) +
        (Fintype.card (RandomGreedy.forwardNeighbors H x) : ℝ) ^ 2 *
          ((N : ℝ) ^
            (Fintype.card (RandomGreedy.forwardNeighbors H x) - 1) * ε) ≤
        meanBound x := by
    intro x
    rfl
  have htail : ∀ x, 0 ≤ tail x := by
    intro x
    have hp : 0 ≤ ∏ y : RandomGreedy.forwardNeighbors H x,
        (q (part y) * (τ : ℝ) / 2) := by
      apply Finset.prod_nonneg
      intro y hy
      exact div_nonneg (mul_nonneg (hqpos (part y)).le (by positivity)) (by norm_num)
    dsimp [tail]
    exact mul_nonneg (div_nonneg hμ.le (by norm_num)) hp
  have hsizeTail : ∀ p, 0 ≤ sizeTail p := by
    intro p
    dsimp [sizeTail]
    exact mul_nonneg (hqpos p).le (by positivity)
  have hsize : ∀ p,
      q p * ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
          Gc A Λ (color p)).card : ℝ) + sizeTail p ≤
        γ * threshold p := by
    intro p
    have hBnat : (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
        Gc A Λ (color p)).card ≤ N := by
      have hs := Finset.card_le_card (Finset.subset_univ
        (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
          Gc A Λ (color p)))
      simpa using hs
    have hB : ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
        Gc A Λ (color p)).card : ℝ) ≤ N := by exact_mod_cast hBnat
    have hlower := TargetWeights.mass_mul_div_eight_le_threshold
      H hd hdeg layer c hlayer (by omega : 0 < L) hQ hτlarge p
    have hNτ : (N : ℝ) ≤ (C + 1 : ℕ) * (τ : ℝ) := by
      have hcoef : C ≤ (C + 1) * T := by
        calc
          C ≤ C + 1 := by omega
          _ ≤ T * (C + 1) := Nat.le_mul_of_pos_left _ hT
          _ = (C + 1) * T := by ac_rfl
      have hnat : N ≤ (C + 1) * τ := by
        dsimp [N, τ]
        calc
          C * a ^ 8 ≤ ((C + 1) * T) * a ^ 8 := Nat.mul_le_mul_right _ hcoef
          _ = (C + 1) * (T * a ^ 8) := by ring
      exact_mod_cast hnat
    dsimp [sizeTail, q, γ]
    have hq0 : (0 : ℝ) ≤ TargetWeights.mass L Q p :=
      (TargetWeights.mass_pos (L := L) hQ p).le
    calc
      TargetWeights.mass L Q p *
          ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
            Gc A Λ (color p)).card : ℝ) + TargetWeights.mass L Q p * N ≤
          2 * (TargetWeights.mass L Q p * N) := by
        calc
          TargetWeights.mass L Q p *
              ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
                Gc A Λ (color p)).card : ℝ) + TargetWeights.mass L Q p * N ≤
              TargetWeights.mass L Q p * N + TargetWeights.mass L Q p * N :=
            add_le_add (mul_le_mul_of_nonneg_left hB hq0) le_rfl
          _ = 2 * (TargetWeights.mass L Q p * N) := by ring
      _ ≤ 2 * (TargetWeights.mass L Q p * ((C + 1 : ℕ) * (τ : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNτ hq0) (by norm_num)
      _ ≤ 16 * ((C : ℝ) + 1) * threshold p := by
        have hmul := mul_le_mul_of_nonneg_left hlower
          (show (0 : ℝ) ≤ 16 * ((C : ℝ) + 1) by positivity)
        calc
          2 * (TargetWeights.mass L Q p * ((C + 1 : ℕ) * (τ : ℝ))) =
              16 * ((C : ℝ) + 1) *
                (TargetWeights.mass L Q p * (τ : ℝ) / 8) := by
            push_cast
            ring
          _ ≤ 16 * ((C : ℝ) + 1) * threshold p := hmul
  have htotal :
      ∑ x : Fin n, (2 / (threshold (part x) : ℝ)) *
        (2 * RandomGreedy.branchCoefficient (2 * γ) D * μ) < 1 := by
    have hsum := TargetWeights.sum_two_div_threshold_le H hd hdeg layer c hlayer
      hL hQ hτlarge
    have hfactor : 2 * RandomGreedy.branchCoefficient (2 * γ) D * μ =
        1 / (64 * Q * L) := by
      dsimp [μ, Bcoef]
      have hbpos : 0 < RandomGreedy.branchCoefficient (2 * γ) D := by
        have hb2 : 0 < 2 * RandomGreedy.branchCoefficient (2 * γ) D := by
          simpa [Bcoef, γ] using hBcoef
        linarith
      have hb : RandomGreedy.branchCoefficient (2 * γ) D ≠ 0 := ne_of_gt hbpos
      field_simp [hb]
    rw [hfactor, ← Finset.sum_mul]
    calc
      (∑ x : Fin n, 2 / (threshold (part x) : ℝ)) * (1 / (64 * Q * L)) ≤
          ((32 : ℝ) * Q * L * n / τ) * (1 / (64 * Q * L)) := by gcongr
      _ ≤ (1 : ℝ) / (2 * T) := by
        have hQL : (0 : ℝ) < (Q : ℝ) * L := by positivity
        have hτR : (0 : ℝ) < τ := by positivity
        have heq : ((32 : ℝ) * Q * L * n / τ) * (1 / (64 * Q * L)) =
            (n : ℝ) / (2 * τ) := by
          field_simp
          ring
        rw [heq]
        have hdenLeft : (0 : ℝ) < 2 * τ := by positivity
        have hdenRight : (0 : ℝ) < 2 * T := by positivity
        apply (div_le_div_iff₀ hdenLeft hdenRight).2
        have hcross : n * T ≤ τ := by
          change n * T ≤ T * a ^ 8
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left T hnA
        have hcross2 : n * (2 * T) ≤ 1 * (2 * τ) := by
          calc
            n * (2 * T) = 2 * (n * T) := by ring
            _ ≤ 2 * τ := Nat.mul_le_mul_left 2 hcross
            _ = 1 * (2 * τ) := by ring
        exact_mod_cast hcross2
      _ < 1 := by
        have : (1 : ℝ) < 2 * T := by exact_mod_cast (show 1 < 2 * T by omega)
        exact (div_lt_one (by positivity)).2 this
  have hBcard : ∀ j, τ ≤
      (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
        Gc A Λ j).card := by
    intro j
    have hsum := PrunedHost.prunedLevels_card_add_bad_ge
      (D := D) (θ := oldθ) (s := 4 * D) Gc A Λ j
    have hAj := hAcard' j
    omega
  have hdiagReserve : 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
      (Q : ℝ) ^ (2 * D) / μ ^ 2 ≤ (a : ℝ) ^ 15 := by
    have hceil : diagK ≤ (Nat.ceil diagK : ℝ) := Nat.le_ceil diagK
    have hceilNat : Nat.ceil diagK ≤ a := by
      have : Nat.ceil diagK + 1 ≤ a := by simpa [a₄] using ha₄a
      omega
    have hdiagA : diagK ≤ (a : ℝ) :=
      hceil.trans (by exact_mod_cast hceilNat)
    have htwoPow : (1 : ℝ) ≤ 2 ^ (2 * D) := one_le_pow₀ (by norm_num)
    have hbase0 : 0 ≤ 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
        (Q : ℝ) ^ (2 * D) / μ ^ 2 := by positivity
    have hbaseDiag : 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
        (Q : ℝ) ^ (2 * D) / μ ^ 2 ≤ diagK := by
      calc
        16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
            (Q : ℝ) ^ (2 * D) / μ ^ 2 =
            (16 * D ^ 4 * C ^ (2 * D) * Q ^ (2 * D) / μ ^ 2) * 1 := by ring
        _ ≤ (16 * D ^ 4 * C ^ (2 * D) * Q ^ (2 * D) / μ ^ 2) *
            2 ^ (2 * D) := mul_le_mul_of_nonneg_left htwoPow hbase0
        _ = diagK := by dsimp [diagK]; ring
    have haPow : (a : ℝ) ≤ (a : ℝ) ^ 15 := by
      exact_mod_cast (Nat.le_pow (by omega : 0 < 15))
    exact hbaseDiag.trans (hdiagA.trans haPow)
  have hnormalized : ∀ x,
      meanBound x + tail x ≤ μ *
        ∏ y : RandomGreedy.forwardNeighbors H x,
          (q (part y) *
            ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
              Gc A Λ (color (part y))).card : ℝ) / 2) := by
    intro x
    let I := RandomGreedy.forwardNeighbors H x
    have hk : Fintype.card I ≤ D := by
      simpa only [I, Fintype.card_coe] using hforward x
    have hmass : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a *
        (∏ y : I, q (part y)) ^ 2 := by
      have hm := FinalTools.prod_mass_sq_mul_scale_ge
        (I := I) H hd hdeg layer c hlayer hD hk hL16 hQ
          (fun y : I => part y)
      simpa only [q, a] using hm
    have hε1 : ε ≤ 1 := by simpa only [Nat.cast_one, inv_one] using hεsmall
    have hn := FinalTools.normalized_estimate
      (I := I) (D := D) (C := C) (T := T) (Q := Q) (a := a)
      (N := N) (τ := τ) (ε := ε) (μ := μ)
      (fun y : I => q (part y))
      (fun y : I =>
        (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
          Gc A Λ (color (part y))).card)
      hk hC1 (show 2 ≤ T by omega) hQ hapos rfl rfl hε.le hε1 hμ
      (fun y => hqpos (part y)) (fun y => hBcard (color (part y)))
      hmainSmall hmass hdiagReserve
    simpa only [meanBound, tail, I] using hn
  have hfail : PrunedEmbedding.failureSum Gc H part color
      (fun j => PrunedHost.prunedLevels
        (D := D) (θ := oldθ) (s := 4 * D) Gc A Λ j)
      q sizeTail Λ tail < 1 := by
    have hf := FailureEstimate.target_failureSum_lt_one
      (n := n) (d := d) (N := N) (r := r) (D := D) (L := L)
      (Q := Q) (T := T) (oldθ := oldθ) (τ := τ) (R := R) (M := M)
      (a := a) (C := C) (lam := lam) (ε := ε) (μ := μ)
      H hd hdeg layer c hlayer Gc color A Λ tail hr hD
      (show 16 ≤ L by dsimp [L, D]; omega) hL16 hQ
      (show 2 ≤ T by omega) hC hapos rfl
      (show 0 < lam by dsimp [lam]; omega) hμ rfl rfl
      (fun _ => rfl) (fun _ => rfl) hnA hNpos holdθ hAcard' hbad
      hMpos hMold hRM hε.le hAmoment' hcommonNumeric
      (fun {_ _} hxy => hcolor _ _ hxy) hforward hBcard
      (by dsimp [M]; exact le_rfl)
      (by
        dsimp [τ]
        exact (Nat.pow_le_pow_right (show 1 ≤ a from hapos) (by omega)).trans
          (Nat.le_mul_of_pos_left _ hT))
      (by simpa only [polyK, c₁] using ha₁ a ha₁')
      (by simpa only [c₁] using ha₂ a ha₂')
      (by simpa only [c₃] using ha₃ a ha₃')
    simpa only [part, q, sizeTail] using hf
  have hcopy : HasCopy H Gc :=
    PrunedEmbedding.hasCopy_of_pruned_all_direction_parameters
      Gc H part color threshold A q Λ tail meanBound sizeTail
      ⟨0, hnpos⟩ ⟨0, by simpa [N] using Nat.mul_pos hC hmpos⟩
      hr hD holdθ hτpos hτold hAcard' hbad hτR hAmoment' hε.le
      hNpos hMpos hMold hRM hcommonNumeric hpart horder hcolor hforward
      hthreshold hpartSize hqpos hqsum hthresholdSample hΛpos hmeanNumeric
      htail hμ.le hnormalized hγ hsizeTail hsize htotal hfail
  have hlift : HasCopy H (HostNested.colorGraph Gbig hostColor) := by
    rcases hcopy with ⟨e⟩
    refine ⟨{
      toFun := fun x => f (e x)
      injective' := f.injective.comp e.injective'
      map_adj' := ?_ }⟩
    intro x y hxy
    have he := e.map_adj' hxy
    cases hostColor <;> simpa [Gc, G, HostNested.colorGraph,
      SimpleGraph.comap_adj, SimpleGraph.compl_adj] using he
  cases hostColor with
  | false => exact Or.inl (by simpa using hlift)
  | true => exact Or.inr (by simpa using hlift)

end

end Erdos163
