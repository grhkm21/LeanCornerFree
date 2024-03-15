import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Nat hiding log sqrt
open Real hiding rpow
open Int Finset Topology Filter Asymptotics

open scoped BigOperators

set_option autoImplicit false

/- def π (q d : ℕ) : S q d → V d := fun n ↦ (fun k ↦ (q.digits n).getD k 0) -/

variable (d : ℕ)

noncomputable def q : ℝ := 2 / sqrt 3

lemma q_pos : 0 < q := div_pos zero_lt_two $ (sqrt_pos.mpr zero_lt_three)

lemma q_nonneg : 0 ≤ q := le_of_lt q_pos

theorem q_lt_2 : q < 2 := by
  apply (_root_.mul_self_lt_mul_self_iff q_nonneg zero_le_two).mpr
  rw [←sq, q, div_pow, sq_sqrt zero_le_three]
  apply (div_lt_iff zero_lt_three).mpr
  norm_num

theorem pow_div_pow_eventuallyEq_atTop' {p q : ℝ} :
    (fun x : ℝ => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ (p - q) := by
  apply (eventually_gt_atTop 0).mono fun x hx => _
  intro x hx
  simp_rw [Real.rpow_sub hx p q]

theorem tendsto_pow_div_pow_atTop_zero' {p q : ℝ}
    (hpq : p < q) : Tendsto (fun x : ℝ => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop']
  /- apply tendsto_rpow_neg_atTop -/
  sorry

/- Testing asymptotics API -/
theorem q_asymptotics : (fun n : ℝ ↦ n ^ q) =o[atTop] fun n ↦ (n ^ 2 : ℝ) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · simp_rw [←Real.rpow_two]
    apply tendsto_pow_div_pow_atTop_zero' q_lt_2
  · rw [eventually_atTop]
    exact ⟨1, fun _ _ h ↦ by simp at h; subst h; apply zero_rpow (_root_.ne_of_gt q_pos) ⟩

/- c^d + 1 = (c + o(1))^d -/
example (c : ℝ) (hc : 1 ≤ c) :
    ∃ f : ℕ → ℝ, (f =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ d, c ^ d + 1 = (c + f d) ^ d := by
  sorry

#check isLittleO_pow_log_id_atTop

#check isLittleO_one_iff
