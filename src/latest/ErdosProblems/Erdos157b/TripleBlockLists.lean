import ErdosProblems.Erdos157.Basic
import Mathlib.Data.List.OfFn

/-! Concatenation preserves a blockwise three-summand identity. -/

namespace Erdos157.Binary

theorem encode_flatten_triple_eq {n : ℕ}
    (x y z w : Fin n → List (ℕ × ℕ))
    (hxy : ∀ i, MixedRadix.place (x i) = MixedRadix.place (y i))
    (hxz : ∀ i, MixedRadix.place (x i) = MixedRadix.place (z i))
    (hxw : ∀ i, MixedRadix.place (x i) = MixedRadix.place (w i))
    (he : ∀ i, MixedRadix.encode (x i) + MixedRadix.encode (y i) +
      MixedRadix.encode (z i) = MixedRadix.encode (w i)) :
    MixedRadix.encode (List.ofFn x).flatten + MixedRadix.encode (List.ofFn y).flatten +
      MixedRadix.encode (List.ofFn z).flatten = MixedRadix.encode (List.ofFn w).flatten := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ) (fun i => w i.succ)
      (fun i => hxy i.succ) (fun i => hxz i.succ) (fun i => hxw i.succ) (fun i => he i.succ)
    simp only [List.ofFn_succ, List.flatten_cons, MixedRadix.encode_append]
    rw [← hxy 0, ← hxz 0, ← hxw 0]
    nlinarith [he 0]

end Erdos157.Binary
