import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Nat hiding log sqrt
open Real Filter Asymptotics Topology

example (f g : ℕ → ℝ) (hf : f =o[atTop] (1 : ℕ → ℝ)) (hg : g =O[atTop] f) :
    g =o[atTop] (1 : ℕ → ℝ) := by
  exact hg.trans_isLittleO hf

lemma af : (fun x ↦ x + 1 : ℕ → ℝ) =O[atTop] (exp · : ℕ → ℝ) := by
  apply isBigO_of_le
  intro x
  iterate 2 rw [norm_eq_abs, abs_eq_self.mpr]
  · exact add_one_le_exp _
  · exact exp_nonneg ↑x
  · linarith

example (f : ℕ → ℝ) (hf : f =o[atTop] (1 : ℕ → ℝ)) :
    (fun x ↦ sqrt (1 / (1 + f x) - 1)) =o[atTop] (1 : ℕ → ℝ) := by
  apply (isLittleO_one_iff _).mpr
  replace hf := (isLittleO_one_iff _).mp hf
  simpa using (((hf.const_add 1).inv₀ (by simp)).sub_const 1).sqrt

example (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : Tendsto (1 / (1 + f)) atTop (𝓝 1) := by
  simpa using (hf.const_add 1).inv₀

example (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : Tendsto (fun x ↦ sqrt (1 / (1 + f x))) atTop (𝓝 1) := by
  simpa using ((hf.const_add 1).inv₀ (by simp)).sqrt

theorem asympt2 {c : ℝ} (hc : 1 < c) :
    ∀ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) →
      ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
        (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
          =ᶠ[atTop] (fun N ↦ (1 + g N) * sqrt (log N / log c)) := by
  intro f hf

  /- Step 1: Rewrite log (c + o(1)) to log(c) + log(1 + o(1)) -/
  have step : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
      (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
        =ᶠ[atTop] (fun N : ℕ ↦ sqrt (log N / (log c + log (1 + g N)))) := by
    use fun N ↦ f N / c
    constructor
    · rw [isLittleO_one_iff] at hf ⊢
      simpa using hf.div_const c
    · /- Since f → 0, ∃ k s.t. N ≥ k → 1 + f N / c > 0 -/
      rw [isLittleO_one_iff, atTop_basis.tendsto_iff (nhds_basis_Ioo_pos _)] at hf
      obtain ⟨N, _, hN⟩ := hf 1 zero_lt_one
      simp_rw [Set.mem_Ici, Set.mem_Ioo, zero_sub, zero_add] at hN
      /- Then we can write log(c + f N) = log(c) + log(1 + f N / c) -/
      rw [EventuallyEq, eventually_atTop]
      use N, fun x hx ↦ ?_
      rw [← log_mul (by linarith), mul_add, mul_div_cancel' _ (by linarith), mul_one]
      have : -1 < -1 / c := by
        rwa [neg_div, neg_lt_neg_iff, div_lt_iff $ zero_lt_one.trans hc, one_mul]
      have : -1 / c < f x / c := (div_lt_div_right $ zero_lt_one.trans hc).mpr (hN x hx).left
      linarith

  /- Step 2: Rewrite log (1 + o(1)) to o(1) -/
  replace step : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
      (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
        =ᶠ[atTop] (fun N : ℕ ↦ sqrt (log N / (log c + g N))) := by
    obtain ⟨g, hg, hg'⟩ := step
    use fun N ↦ log (1 + g N), ?_, hg'
    rw [isLittleO_one_iff] at hg ⊢
    have : ContinuousAt log 1 := continuousAt_log one_ne_zero
    convert Tendsto.comp (continuousAt_log one_ne_zero) (by simpa using hg.const_add 1)
    exact log_one.symm

  /- Step 3: Isolate asymptotic term from constant factor -/
  replace step : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
      (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
        =ᶠ[atTop] (fun N : ℕ ↦ sqrt (1 / (1 + g N)) * sqrt (log N / log c)) := by
    obtain ⟨g, hg, hg'⟩ := step
    use fun N ↦ g N / log c, ?_
    · rw [EventuallyEq, eventually_atTop] at hg' ⊢
      obtain ⟨N, hN⟩ := hg'
      use max N 1, fun b hb ↦ ?_
      rw [mul_comm, ← sqrt_mul, mul_one_div, div_div, mul_add, mul_one, mul_div_cancel']
      · exact hN b (le_of_max_le_left hb)
      · apply log_eq_zero.not.mpr
        push_neg
        use ?_, ?_, ?_ <;> linarith [hc]
      · apply div_nonneg
        · have hb' := le_of_max_le_right hb
          refine (log_nonneg_iff ?_).mpr (by simpa using hb')
          simpa only [cast_pos] using hb'
        · exact (log_nonneg_iff (by linarith)).mpr hc.le
    · rw [isLittleO_one_iff] at hg ⊢
      simpa using hg.div_const (log c)

  /- Step 4: Rewrite sqrt (1 / (1 + o(1))) as (1 + o(1)) -/
  replace step : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
      (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
        =ᶠ[atTop] (fun N : ℕ ↦ (1 + g N) * sqrt (log N / log c)) := by
    obtain ⟨g, hg, hg'⟩ := step
    use fun N ↦ sqrt (1 / (1 + g N)) - 1, ?_
    · rw [EventuallyEq, eventually_atTop] at hg' ⊢
      obtain ⟨N, hN⟩ := hg'
      simp_rw [add_sub_cancel'_right]
      exact ⟨N, hN⟩
    · rw [isLittleO_one_iff] at hg ⊢
      simpa using ((hg.const_add 1).inv₀ (by linarith)).sqrt.sub_const 1

  exact step
