import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace DesignExistence

/-- Above the explicit size bound, the divisibility conditions guarantee a
family of uniform blocks covering every smaller uniform subset exactly once. -/
theorem designs_exist {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : (4 * q) ^ (90 * q * (2 * q) ^ r * (6 * q.choose r) ^ 2) ≤ n)
    (hdiv : ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i)) :
    ∃ D : Finset (Finset (Fin n)),
      (∀ Q ∈ D, Q.card = q) ∧
      ∀ e : Finset (Fin n), e.card = r → ∃! Q : Finset (Fin n), Q ∈ D ∧ e ⊆ Q := by
  sorry

end DesignExistence
