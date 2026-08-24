import ErdosProblems.Erdos587.PolynomialDenseRows

/-!
Polynomial-count mixed filling in a coefficient box. The dimension
induction retains the previous density loss `(4*D)^d` but uses only
`d*denseRowCount D`, hence at most `256*d*D^4`, distinct summands.
-/

open scoped Pointwise

namespace Erdos587.CFP

def denseBoxCount (D : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => denseBoxCount D d + denseRowCount D

theorem denseBoxCount_eq_mul (D d : ℕ) : denseBoxCount D d = d * denseRowCount D := by
  induction d with
  | zero => simp [denseBoxCount]
  | succ d ih => rw [denseBoxCount, ih]; ring

theorem denseBoxCount_le {D : ℕ} (hD : 0 < D) (d : ℕ) :
    denseBoxCount D d ≤ 256 * d * D ^ 4 := by
  rw [denseBoxCount_eq_mul]
  calc
    d * denseRowCount D ≤ d * (256 * D ^ 4) := Nat.mul_le_mul_left d (denseRowCount_le hD)
    _ = 256 * d * D ^ 4 := by ring

/-- Polynomially many dense lattice summands fill a proper axis-aligned
progression occupying a controlled fraction of the coefficient box. -/
theorem exists_large_coordinate_GAP_of_dense_summands
    {d : ℕ} (D : ℕ) (hD : 0 < D) (L : Fin d → ℕ)
    (Xs : List (Finset (Fin d → ℤ)))
    (hlen : Xs.length = denseBoxCount D d)
    (hXs : ∀ X ∈ Xs, X ⊆ nvCoordBox L)
    (hdense : ∀ X ∈ Xs, (nvCoordBox L).card ≤ D * X.card) :
    ∃ P : NVFullGAP d,
      P.Proper ∧ P.AxisAligned ∧ P.carrier ⊆ nvFinsetListSum Xs ∧
      (nvCoordBox L).card ≤ nvDenseFactor D d * P.carrier.card := by
  induction d with
  | zero =>
      have hnil : Xs = [] := List.length_eq_zero_iff.mp (by
        simpa [denseBoxCount] using hlen)
      subst Xs
      refine ⟨NVFullGAP.point, NVFullGAP.point_proper,
        NVFullGAP.point_axisAligned, ?_, ?_⟩
      · intro v hv
        rw [NVFullGAP.mem_carrier_iff] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        simp [NVFullGAP.eval, NVFullGAP.point, nvFinsetListSum]
      · rw [card_nvCoordBox,
          NVFullGAP.card_carrier_of_proper _ NVFullGAP.point_proper]
        simp [nvDenseFactor, NVFullGAP.point]
  | succ d ih =>
      let L₀ : Fin d → ℕ := Fin.init L
      let H : ℕ := L (Fin.last d)
      have hL : Fin.snoc L₀ H = L := Fin.snoc_init_self L
      let n := denseBoxCount D d
      let m := denseRowCount D
      let Xh := Xs.take n
      let Xv := Xs.drop n
      have hlen' : Xs.length = n + m := by
        simpa only [n, m, denseBoxCount] using hlen
      have hnle : n ≤ Xs.length := by
        rw [hlen']
        exact Nat.le_add_right _ _
      have hXhLen : Xh.length = denseBoxCount D d := by
        dsimp [Xh, n]
        rw [List.length_take_of_le hnle]
      have hXvLen : Xv.length = denseRowCount D := by
        dsimp [Xv, n, m] at hlen' ⊢
        rw [List.length_drop, hlen']
        simp
      have hXhSub : ∀ X ∈ Xh, X ⊆ nvCoordBox (Fin.snoc L₀ H) := by
        intro X hX
        rw [hL]
        exact hXs X (List.mem_of_mem_take hX)
      have hXhDense : ∀ X ∈ Xh,
          (nvCoordBox (Fin.snoc L₀ H)).card ≤ D * X.card := by
        intro X hX
        rw [hL]
        exact hdense X (List.mem_of_mem_take hX)
      obtain ⟨Us, zs, hrelH, hUs⟩ := exists_nvLastFiberLists Xh hXhSub hXhDense
      have hUsLen : Us.length = denseBoxCount D d := by
        rw [← hrelH.length_eq_left_middle, hXhLen]
      obtain ⟨P, hPproper, hPaxis, hPsub, hPcard⟩ :=
        ih L₀ Us hUsLen (fun U hU => (hUs U hU).1) (fun U hU => (hUs U hU).2)
      have hXvSub : ∀ X ∈ Xv, X ⊆ nvCoordBox (Fin.snoc L₀ H) := by
        intro X hX
        rw [hL]
        exact hXs X (List.mem_of_mem_drop hX)
      have hXvDense : ∀ X ∈ Xv,
          (nvCoordBox (Fin.snoc L₀ H)).card ≤ D * X.card := by
        intro X hX
        rw [hL]
        exact hdense X (List.mem_of_mem_drop hX)
      obtain ⟨rows, us, hrelV, hrows⟩ := exists_nvInitFiberLists Xv hXvSub hXvDense
      have hrowsLen : rows.length = denseRowCount D := by
        rw [← hrelV.length_eq_left_middle, hXvLen]
      obtain ⟨a, q, R, hq, hRcard, hAP⟩ :=
        exists_dense_intAP_of_different_rows_polynomial hD rows hrowsLen hrows
      let Q : NVFullGAP (d + 1) := NVFullGAP.snocAP P us.sum zs.sum a q R
      have hQproper : Q.Proper := NVFullGAP.proper_snocAP P hPproper us.sum zs.sum a q hq R
      have hQaxis : Q.AxisAligned := NVFullGAP.axisAligned_snocAP P hPaxis us.sum zs.sum a q R
      have hsplit : Xs = Xh ++ Xv := (List.take_append_drop n Xs).symm
      refine ⟨Q, hQproper, hQaxis, ?_, ?_⟩
      · intro v hv
        rw [NVFullGAP.mem_carrier_iff] at hv
        obtain ⟨c, hcbox, rfl⟩ := hv
        rw [NVFullGAP.coeffBox, Finset.mem_Icc, Pi.le_def] at hcbox
        have hxbox : Fin.init c ∈ P.coeffBox := by
          rw [NVFullGAP.coeffBox, Finset.mem_Icc, Pi.le_def]
          exact ⟨fun i => hcbox.1 i.castSucc, fun i => by
            change c i.castSucc ≤ P.length i
            simpa [Q, NVFullGAP.snocAP] using hcbox.2 i.castSucc⟩
        have hyLe : c (Fin.last d) ≤ R := by
          simpa [Q, NVFullGAP.snocAP] using hcbox.2 (Fin.last d)
        have hpCarrier : P.eval (Fin.init c) ∈ P.carrier :=
          NVFullGAP.mem_carrier_iff.mpr ⟨Fin.init c, hxbox, rfl⟩
        have hh := nvFinsetListSum_snoc_fibers_subset hrelH
          (P.eval (Fin.init c)) (hPsub hpCarrier)
        have hvrow := hAP (c (Fin.last d)) hyLe
        have hv' := nvFinsetListSum_snoc_rows_subset hrelV
          (a + (c (Fin.last d) : ℤ) * q) hvrow
        rw [hsplit, nvFinsetListSum_append, Finset.mem_add]
        refine ⟨Fin.snoc (P.eval (Fin.init c)) zs.sum, hh,
          Fin.snoc us.sum (a + (c (Fin.last d) : ℤ) * q), hv', ?_⟩
        change _ = (NVFullGAP.snocAP P us.sum zs.sum a q R).eval c
        conv_rhs => rw [← Fin.snoc_init_self c]
        rw [NVFullGAP.eval_snocAP]
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp <;> ring
      · rw [← hL, card_nvCoordBox_snoc]
        have hQcard : Q.carrier.card = P.carrier.card * (R + 1) :=
          NVFullGAP.card_carrier_snocAP P hPproper us.sum zs.sum a q hq R
        calc
          (nvCoordBox L₀).card * (H + 1) ≤
              (nvDenseFactor D d * P.carrier.card) * (4 * D * (R + 1)) :=
            Nat.mul_le_mul hPcard hRcard
          _ = nvDenseFactor D (d + 1) * Q.carrier.card := by
            rw [nvDenseFactor, hQcard]
            ring

end Erdos587.CFP
