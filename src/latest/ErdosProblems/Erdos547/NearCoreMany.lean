import ErdosProblems.Erdos547.EscapeRamsey
import ErdosProblems.Erdos547.PrefixPotential

/-!
# The many-nonleaves near-core case

The escape hypothesis is discharged here using the two dense-configuration
cases. Integer size and numerical decay estimates remain explicit.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem ramsey_of_near_core_many_nonleaves {m : ℕ}
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree) (R : SimpleGraph (Fin (2 * m)))
    (S : Set (Fin (2 * m))) [Fintype S] [Nonempty S]
    (d k t r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hm : 20000 * (3 * (d + k + t) + k) ≤ m)
    (hbudget : m * (d + k) ≤ t ^ 2)
    (hdegree : ∀ z : S, m ≤ (R.induce S).degree z + d)
    (hcore : 2 * r ≤ Fintype.card (treeCore T)) (hN : k ≤ Fintype.card S)
    (hsmall : 4 * r ≤ k) (hmin : 2 * r ≤ (R.induce S).minDegree)
    (hthreshold : pairDecay (Fintype.card S) k ^ (r - 1) * Fintype.card S < (1 / 2 : ℝ) ^ d) :
    T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  let : DecidableEq S := fun a b ↦ Classical.propDecidable (a = b)
  rcases ramsey_or_induced_escape T hT R S d k t hk hm hbudget hdegree with hmono | hescape
  · exact hmono
  obtain ⟨f⟩ := isContained_of_escape_many_nonleaves (G := R.induce S) hT m d r k
    (Fintype.card_fin (m + 1)) hr hcore hN hsmall hmin hdegree hescape hthreshold
  exact Or.inl ⟨(SimpleGraph.Copy.induce R S).comp f⟩

end Erdos547

#print axioms Erdos547.ramsey_of_near_core_many_nonleaves
