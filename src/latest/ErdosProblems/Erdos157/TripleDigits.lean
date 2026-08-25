import ErdosProblems.Erdos157.PairedTargets

/-! Absorbing the carry from a sum of three data digits. -/

namespace Erdos157.Elementary

theorem PairedTargets.Digit.realize {b : ℕ} [NeZero b] (d : PairedTargets.Digit b)
    (x y z : ZMod b) (hsum : x + y + z = (d.data.val : ZMod b)) :
    ∃ a c e : AuxiliaryDigit,
      PairDigits.pack b x.val a + PairDigits.pack b y.val c + PairDigits.pack b z.val e = d.value := by
  have hb : 0 < b := NeZero.pos b
  let κ := (x.val + y.val + z.val) / b
  have hκ : κ ≤ 2 := by
    simpa only [add_zero] using MixedRadix.three_digit_carry_le_two hb
      (ZMod.val_lt x) (ZMod.val_lt y) (ZMod.val_lt z) (Nat.zero_le 2)
  have hcast : ((x.val + y.val + z.val : ℕ) : ZMod b) = (d.data.val : ZMod b) := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hsum
  have hmod : (x.val + y.val + z.val) % b = d.data.val := by
    have hv := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt d.data.isLt] using hv
  have hdecomp : x.val + y.val + z.val = d.data.val + b * κ := by
    have hn := Nat.mod_add_div (x.val + y.val + z.val) b
    rw [hmod] at hn
    exact hn.symm
  obtain ⟨a, ha, c, hc, e, he, haux⟩ := d.aux_carryCovered κ hκ
  refine ⟨⟨a, ha⟩, ⟨c, hc⟩, ⟨e, he⟩, ?_⟩
  dsimp only [PairDigits.pack, PairedTargets.Digit.value]
  nlinarith

theorem encode_ofFn_triple_sum {n : ℕ} (b x y z : Fin n → ℕ) :
    MixedRadix.encode (List.ofFn (fun i => (b i, x i + y i + z i))) =
      MixedRadix.encode (List.ofFn (fun i => (b i, x i))) +
      MixedRadix.encode (List.ofFn (fun i => (b i, y i))) +
      MixedRadix.encode (List.ofFn (fun i => (b i, z i))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, MixedRadix.encode_cons]
    rw [ih (fun i => b i.succ) (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ)]
    ring

theorem encode_ofFn_triple_eq {n : ℕ} (b x y z w : Fin n → ℕ)
    (h : ∀ i, x i + y i + z i = w i) :
    MixedRadix.encode (List.ofFn (fun i => (b i, x i))) +
      MixedRadix.encode (List.ofFn (fun i => (b i, y i))) +
      MixedRadix.encode (List.ofFn (fun i => (b i, z i))) =
      MixedRadix.encode (List.ofFn (fun i => (b i, w i))) := by
  rw [← encode_ofFn_triple_sum]
  simp only [h]

theorem three_top_digits {Q z : ℕ} (hQ : 0 < Q) (hzlo : 3 ≤ z) (hzhi : z ≤ 3 * Q) :
    ∃ t₁ t₂ t₃ : Fin Q, (1 + t₁.val) + (1 + t₂.val) + (1 + t₃.val) = z := by
  let a := min (z - 3) (Q - 1)
  let b := min (z - 3 - a) (Q - 1)
  let c := z - 3 - a - b
  have ha : a < Q := by dsimp only [a]; omega
  have hb : b < Q := by dsimp only [b]; omega
  have hc : c < Q := by dsimp only [c, b, a]; omega
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ?_⟩
  dsimp only [a, b, c]
  omega

end Erdos157.Elementary
