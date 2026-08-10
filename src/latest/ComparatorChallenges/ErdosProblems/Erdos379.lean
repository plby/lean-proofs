import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Prime.Defs

namespace Erdos379

open Filter

noncomputable def S (n : ℕ) : ℕ :=
  sSup {s | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p ^ s ∣ n.choose k}
namespace depth_0_lemma_1

end depth_0_lemma_1

namespace depth_0_lemma_2

end depth_0_lemma_2

namespace depth_0_lemma_3

end depth_0_lemma_3

namespace depth_0_lemma_4
end depth_0_lemma_4

namespace depth_0_lemma_5

end depth_0_lemma_5

end Erdos379

attribute [local instance] Classical.propDecidable

theorem Erdos379.erdos_379 :
    @Eq.{1} ENat
      (@Filter.limsup.{0, 0} ENat Nat
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENat
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENat
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENat
              instCompleteLinearOrderENat)))
        (fun (n : Nat) ↦ @Nat.cast.{0} ENat ENat.instNatCast (Erdos379.S n))
        (@Filter.atTop.{0} Nat Nat.instPreorder))
      (@Top.top.{0} ENat instTopENat)
  := by
  sorry
