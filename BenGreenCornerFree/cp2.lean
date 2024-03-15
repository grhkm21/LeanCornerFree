import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Nat hiding log sqrt
open Real Filter Asymptotics Topology

variable {c : ℝ} (hc : 1 < c) (f : ℕ → ℝ) (hf : f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ))

/- Step 1: Rewrite log (c + o(1)) to log(c) + log(1 + o(1)) -/
lemma aux1 : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
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
lemma aux2 : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
    (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
      =ᶠ[atTop] (fun N : ℕ ↦ sqrt (log N / (log c + g N))) := by
  obtain ⟨g, hg, hg'⟩ := aux1 hc f hf
  use fun N ↦ log (1 + g N), ?_, hg'
  rw [isLittleO_one_iff] at hg ⊢
  have : ContinuousAt log 1 := continuousAt_log one_ne_zero
  convert Tendsto.comp (continuousAt_log one_ne_zero) (by simpa using hg.const_add 1)
  exact log_one.symm

/- Step 3: Isolate asymptotic term from constant factor -/
lemma aux3 : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
    (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
      =ᶠ[atTop] (fun N : ℕ ↦ sqrt (1 / (1 + g N)) * sqrt (log N / log c)) := by
  obtain ⟨g, hg, hg'⟩ := aux2 hc f hf
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
lemma aux4 : ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
    (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
      =ᶠ[atTop] (fun N : ℕ ↦ (1 + g N) * sqrt (log N / log c)) := by
  obtain ⟨g, hg, hg'⟩ := aux3 hc f hf
  use fun N ↦ sqrt (1 / (1 + g N)) - 1, ?_
  · rw [EventuallyEq, eventually_atTop] at hg' ⊢
    obtain ⟨N, hN⟩ := hg'
    simp_rw [add_sub_cancel'_right]
    exact ⟨N, hN⟩
  · rw [isLittleO_one_iff] at hg ⊢
    simpa using ((hg.const_add 1).inv₀ (by linarith)).sqrt.sub_const 1

theorem asympt2 {c : ℝ} (hc : 1 < c) : ∀ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) →
    ∃ g : ℕ → ℝ, g =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧
      (fun N : ℕ ↦ sqrt (log N / log (c + f N)))
        =ᶠ[atTop] (fun N ↦ (1 + g N) * sqrt (log N / log c)) := by
  intro f hf
  exact aux4 hc f hf
