import Wikipedia.HopfProblem.OrbitPairCompactTransportSubdivision
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Compact homotopy lifting from continuous local fibre transport

The transport is required to be the identity on the diagonal. Finite
time subdivision then lifts compact homotopies while fixing every
stationary parameter, including any prescribed cube boundary.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.OrbitPair

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

structure LocalTransport (p : E → B) where
  domain : TopologicalSpace.Opens (B × B)
  diagonal : ∀ b, (b, b) ∈ domain
  transport : C({z : E × B // (p z.1, z.2) ∈ domain}, E)
  project : ∀ z, p (transport z) = z.val.2
  self : ∀ x, transport ⟨(x, p x), diagonal (p x)⟩ = x

namespace LocalTransport

variable {p : E → B} (T : LocalTransport p)

theorem apply_eq_self (z : {z : E × B // (p z.1, z.2) ∈ T.domain})
    (hz : z.val.2 = p z.val.1) : T.transport z = z.val.1 := by
  have he : z = ⟨(z.val.1, p z.val.1), T.diagonal (p z.val.1)⟩ :=
    Subtype.ext (Prod.ext rfl hz)
  conv_lhs => rw [he]
  exact T.self z.val.1

variable {X : Type*} [TopologicalSpace X]
  (H : C(I × X, B)) (s u : I) (hsu : s ≤ u)
  (hclose : ∀ t ∈ Icc s u, ∀ x, (H (s, x), H (t, x)) ∈ T.domain)
  (a : C(I × X, E)) (ha : ∀ t x, p (a (t, x)) = H (min t s, x))

include hsu hclose ha in
theorem step_mem_domain (z : I × X) :
    (p (a (min z.1 s, z.2)), H (min z.1 u, z.2)) ∈ T.domain := by
  rw [ha, min_eq_left (min_le_right z.1 s)]
  by_cases ht : z.1 ≤ s
  · rw [min_eq_left ht, min_eq_left (ht.trans hsu)]
    exact T.diagonal _
  · have hst : s ≤ z.1 := le_of_not_ge ht
    rw [min_eq_right hst]
    exact hclose (min z.1 u) ⟨le_min hst hsu, min_le_right _ _⟩ z.2

def stepInput : C(I × X, {z : E × B // (p z.1, z.2) ∈ T.domain}) where
  toFun z := ⟨(a (min z.1 s, z.2), H (min z.1 u, z.2)),
    T.step_mem_domain H s u hsu hclose a ha z⟩
  continuous_toFun :=
    ((a.continuous.comp ((continuous_fst.min continuous_const).prodMk continuous_snd)).prodMk
      (H.continuous.comp ((continuous_fst.min continuous_const).prodMk continuous_snd))).subtype_mk _

def step : C(I × X, E) := T.transport.comp (T.stepInput H s u hsu hclose a ha)

theorem step_project (t : I) (x : X) :
    p (T.step H s u hsu hclose a ha (t, x)) = H (min t u, x) := T.project _

theorem step_before (t : I) (x : X) (ht : t ≤ s) :
    T.step H s u hsu hclose a ha (t, x) = a (t, x) := by
  have hz := T.apply_eq_self (T.stepInput H s u hsu hclose a ha (t, x))
  have he : (T.stepInput H s u hsu hclose a ha (t, x)).val.2 =
      p (T.stepInput H s u hsu hclose a ha (t, x)).val.1 := by
    change H (min t u, x) = p (a (min t s, x))
    rw [ha, min_eq_left (min_le_right t s), min_eq_left ht, min_eq_left (ht.trans hsu)]
  have hh := hz he
  change T.step H s u hsu hclose a ha (t, x) = a (min t s, x) at hh
  rw [min_eq_left ht] at hh
  exact hh

theorem step_stationary (a₀ : C(X, E)) (x : X)
    (hH : ∀ t, H (t, x) = H (0, x)) (hfix : ∀ t, a (t, x) = a₀ x) (t : I) :
    T.step H s u hsu hclose a ha (t, x) = a₀ x := by
  have he : (T.stepInput H s u hsu hclose a ha (t, x)).val.2 =
      p (T.stepInput H s u hsu hclose a ha (t, x)).val.1 := by
    change H (min t u, x) = p (a (min t s, x))
    rw [ha]
    exact (hH (min t u)).trans (hH (min (min t s) s)).symm
  exact (T.apply_eq_self _ he).trans (hfix (min t s))

variable [CompactSpace X]

include T in
/-- Compact homotopies lift with prescribed initial lift and all stationary parameters fixed. -/
theorem exists_lift_stationary (a₀ : C(X, E)) (ha₀ : ∀ x, p (a₀ x) = H (0, x)) :
    ∃ G : C(I × X, E), (∀ x, G (0, x) = a₀ x) ∧
      (∀ t x, p (G (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = a₀ x := by
  obtain ⟨τ, hτ₀, hmono, ⟨N, hN⟩, hclose⟩ :=
    exists_compact_transport_subdivision H T.domain T.domain.isOpen T.diagonal
  have hex : ∀ i, ∃ G : C(I × X, E), (∀ x, G (0, x) = a₀ x) ∧
      (∀ t x, p (G (t, x)) = H (min t (τ i), x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = a₀ x := by
    intro i
    induction i with
    | zero =>
      refine ⟨a₀.comp ⟨Prod.snd, continuous_snd⟩, fun _ => rfl, ?_, fun _ _ _ => rfl⟩
      intro t x
      change p (a₀ x) = H (min t (τ 0), x)
      simpa only [hτ₀, min_eq_right (show (0 : I) ≤ t from bot_le)] using ha₀ x
    | succ i ih =>
      obtain ⟨G, hG₀, hGp, hGfix⟩ := ih
      refine ⟨T.step H (τ i) (τ (i + 1)) (hmono i.le_succ) (hclose i) G hGp, ?_,
        T.step_project H (τ i) (τ (i + 1)) (hmono i.le_succ) (hclose i) G hGp, ?_⟩
      · intro x
        rw [T.step_before H (τ i) (τ (i + 1)) (hmono i.le_succ) (hclose i) G hGp 0 x bot_le]
        exact hG₀ x
      · intro x hx t
        exact T.step_stationary H (τ i) (τ (i + 1)) (hmono i.le_succ) (hclose i) G hGp
          a₀ x hx (hGfix x hx) t
  obtain ⟨G, hG₀, hGp, hGfix⟩ := hex N
  refine ⟨G, hG₀, ?_, hGfix⟩
  intro t x
  simpa only [hN N le_rfl, min_eq_left (show t ≤ (1 : I) from le_top)] using hGp t x

end LocalTransport

end Wikipedia.HopfProblem.OrbitPair
