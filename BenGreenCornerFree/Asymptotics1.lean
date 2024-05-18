import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/- def V (n : ℕ) := Fin n → ℤ -/
/- #synth AddCommMonoid (V 5) -/
/- #check Pi.addCommMonoid -/
/- #synth AddCommMonoid ℤ -/

open Set Real Topology Filter Asymptotics

/- TODO: Generalise -/
lemma pow_add_mul_self_le_pow_one_add
    {a b : ℝ} (c : ℕ) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    a ^ c + c * b ≤ (a + b) ^ c := by
  by_cases hc : 0 < c
  · have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [show a + b = a * (1 + b / a) by rw [mul_add, mul_one, mul_div_cancel₀ b (by linarith)],
      mul_pow]
    refine le_trans ?_ ?_ (b := a ^ c * (1 + c * (b / a)))
    · rw [mul_add, mul_one, ← mul_one (c * b), mul_div, mul_div, mul_comm (a ^ c), ← mul_div]
      gcongr
      rw [le_div_iff ha', one_mul]
      exact le_self_pow ha (Nat.not_eq_zero_of_lt hc)
    · gcongr
      rw [← rpow_natCast]
      refine one_add_mul_self_le_rpow_one_add ?_ (Nat.one_le_cast.mpr hc)
      exact (show (-1 : ℝ) ≤ 0 by norm_num).trans (by positivity)
  · norm_num at hc
    subst hc
    norm_num

lemma aux_part1 (c : ℝ) (hc : 1 ≤ c) :
    ∃ f : ℕ → ℝ, 0 ≤ f ∧ (∀ d, 1 ≤ d → c ^ d + 1 = (c + f d) ^ d) := by
  suffices ∀ d : ℕ, 1 ≤ d → ∃ f : ℝ, f ≥ 0 ∧ c ^ d + 1 = (c + f) ^ d by
    use fun d ↦ if hd : 1 ≤ d then Classical.choose (this d hd) else 0
    constructor
    · intro d
      simp only [Pi.zero_apply]
      by_cases hd : 1 ≤ d <;> simp only [hd, dite_true, dite_false]
      · exact (Classical.choose_spec (this d hd)).left
      · rfl
    · intro d hd
      simp only [hd, dite_true]
      exact (Classical.choose_spec (this d hd)).right
  intro d hd
  have h₁ : c ^ d ≤ c ^ d + 1 := (lt_add_one _).le
  have h₂ : c ^ d + 1 ≤ (c + 1) ^ d := by
    refine (add_le_add_left (Nat.one_le_cast.mpr hd) (c ^ d)).trans ?_
    convert pow_add_mul_self_le_pow_one_add d hc zero_le_one
    rw [mul_one]
  have := intermediate_value_Icc (lt_add_one c).le (continuousOn_pow d)
  obtain ⟨f, ⟨hf₁, hf₂⟩⟩ := this (mem_Icc.mpr ⟨h₁, h₂⟩)
  use f - c, ?_, ?_
  · rw [ge_iff_le, sub_nonneg]
    exact (mem_Icc.mp hf₁).left
  · beta_reduce at hf₂
    rw [← add_sub_assoc, add_sub_cancel_left, hf₂]

lemma aux_part2 (c : ℝ) (hc : 1 ≤ c) :
    ∀ f : ℕ → ℝ, (0 ≤ f ∧ ∀ d, 1 ≤ d → c ^ d + 1 = (c + f d) ^ d) → (f =o[atTop] (1 : ℕ → ℝ)) := by
  intro f ⟨hf₁, hf₂⟩
  have {d} (hd : 1 ≤ d) : (c + f d) ^ d ≤ (c + 1 / (d : ℝ)) ^ d := by
    rw [← hf₂ d hd]
    have : c + 1 / (d : ℝ) = c * (1 + 1 / (c * d : ℝ)) := by
      rw [mul_add, mul_one, div_mul_eq_div_div, mul_div, mul_one_div_cancel (by linarith)]
    convert pow_add_mul_self_le_pow_one_add d hc ?_
    · rw [mul_one_div_cancel (by positivity)]
    · norm_num

  have : ∀ᶠ d in atTop, ‖f d‖ ≤ ‖1 / (d : ℝ)‖ := by
    simp_rw [norm_eq_abs, eventually_atTop]
    refine ⟨1, fun d hd ↦ ?_⟩
    specialize this hd
    rw [abs_eq_self.mpr (hf₁ _), abs_eq_self.mpr (by norm_num)]
    contrapose! this
    gcongr

  refine IsBigO.trans_isLittleO (IsBigO.of_bound' this) ?_
  simp_rw [Pi.one_def, isLittleO_iff, eventually_atTop, norm_div, norm_one, mul_one,
    RCLike.norm_natCast]
  intro c hc
  use max 1 ⌈1 / c⌉₊
  intro b hb
  refine (one_div_le ?_ hc).mpr ?_
  · exact Nat.cast_pos.mpr $ le_of_max_le_left hb
  · exact Nat.ceil_le.mp $ le_of_max_le_right hb

lemma aux (c : ℝ) (hc : 1 ≤ c) :
    ∃ f : ℕ → ℝ, f =o[atTop] (1 : ℕ → ℝ) ∧ (∀ d, 1 ≤ d → c ^ d + 1 = (c + f d) ^ d) := by
  obtain ⟨f, hf⟩ := aux_part1 c hc
  use f, aux_part2 c hc f hf, hf.right

lemma aux' (c : ℝ) (hc : 1 ≤ c) :
    ∃ f : ℕ → ℝ, f =o[atTop] (1 : ℕ → ℝ) ∧ ((fun d ↦ c ^ d + 1) =ᶠ[atTop] (fun d ↦ (c + f d) ^ d)) := by
  obtain ⟨f, hf⟩ := aux c hc
  use f, hf.left
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  use 1, hf.right
