import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace MO509164

def f (i : Fin 2) (r : ℝ) (x : ℝ) : ℝ :=
  if i = 0 then r * x else 1 - r + r * x

def f_word (u : List (Fin 2)) (r : ℝ) : ℝ → ℝ :=
  match u with
  | [] => id
  | i :: rest => f i r ∘ f_word rest r

def I_word (u : List (Fin 2)) (r : ℝ) : Set ℝ :=
  (f_word u r) '' Set.Icc 0 1

def Sigma_n (n : ℕ) : Set (List (Fin 2)) :=
  {u | u.length = n}

def C_n (r : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ u ∈ Sigma_n n, I_word u r

def C (r : ℝ) : Set ℝ :=
  ⋂ n, C_n r n

noncomputable def pi (r : ℝ) (ω : ℕ → Fin 2) : ℝ :=
  (1 - r) * ∑' n : ℕ, (ω n : ℝ) * r ^ n

def C_plus (rho : ℝ) : Set ℝ :=
  ⋂ (ε : ℝ) (_ : ε > 0), ⋃ (r : ℝ) (_ : r ∈ Set.Ioo (rho - ε) rho), C r

def C_minus (rho : ℝ) : Set ℝ :=
  ⋂ (ε : ℝ) (_ : ε > 0), ⋃ (r : ℝ) (_ : r ∈ Set.Ioo rho (rho + ε)), C r

def append_zeros (u : List (Fin 2)) : ℕ → Fin 2 :=
  fun n => match u[n]? with
    | some x => x
    | none => 0

def append_ones (u : List (Fin 2)) : ℕ → Fin 2 :=
  fun n => match u[n]? with
    | some x => x
    | none => 1

def E_plus (rho : ℝ) : Set ℝ :=
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 0 ∧
    x = pi rho (append_ones u)} ∪
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 1 ∧
    x = pi rho (append_zeros u)}

open scoped ENNReal

open Topology Filter Metric MeasureTheory

noncomputable def N_delta (E : Set ℝ) (δ : ℝ) : ℕ :=
  sInf {n | ∃ (U : Fin n → Set ℝ),
    (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ) ∧ E ⊆ ⋃ i, U i}

noncomputable def lower_box_dim (E : Set ℝ) : ℝ :=
  Filter.liminf (fun δ => Real.log (N_delta E δ) / -Real.log δ)
    (nhdsWithin 0 (Set.Ioi 0))

noncomputable def upper_box_dim (E : Set ℝ) : ℝ :=
  Filter.limsup (fun δ => Real.log (N_delta E δ) / -Real.log δ)
    (nhdsWithin 0 (Set.Ioi 0))

def E_minus (rho : ℝ) : Set ℝ :=
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 0 ∧
    (1 : Fin 2) ∈ u ∧ x = pi rho (append_zeros u)} ∪
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 1 ∧
    (0 : Fin 2) ∈ u ∧ x = pi rho (append_ones u)}

theorem theorem_minus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    C_minus rho = C rho \ E_minus rho := by
  sorry

theorem theorem_plus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    C_plus rho = C rho \ E_plus rho := by
  sorry

theorem corollary_dimensions_limsup
    (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    let s := Real.log 2 / -Real.log rho
    dimH (C_plus rho) = ENNReal.ofReal s ∧
    dimH (C_minus rho) = ENNReal.ofReal s ∧
    lower_box_dim (C_plus rho) = s ∧
    upper_box_dim (C_plus rho) = s ∧
    lower_box_dim (C_minus rho) = s ∧
    upper_box_dim (C_minus rho) = s := by
  sorry

end MO509164
