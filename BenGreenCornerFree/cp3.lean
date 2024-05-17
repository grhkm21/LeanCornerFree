import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat hiding log sqrt
open Real Filter Asymptotics Topology Set

variable {c : ℝ} (hc : 1 < c) (r : ℝ)
  {f g : ℕ → ℝ} (hf : f =o[atTop] (fun _ ↦ (1 : ℝ))) (hg : g =o[atTop] (fun _ ↦ (1 : ℝ)))

/- Missing Mathlib: continuousAt_logb -/
theorem continuousAt_logb {x b : ℝ} (hx : x ≠ 0) : ContinuousAt (logb b) x :=
  (continuousAt_log hx).div_const b.log

theorem Filter.Tendsto.logb {α : Type*} {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x))
    (hx : x ≠ 0) (b) :
    Tendsto (fun x => logb b (f x)) l (𝓝 (logb b x)) :=
  ((continuousAt_log hx).div_const b.log).tendsto.comp h

lemma useful_aux : ∃ a, ∀ b ≥ a, 0 < 1 + f b := by
  rw [isLittleO_one_iff, atTop_basis.tendsto_iff (nhds_basis_Ioo_pos _)] at hf
  obtain ⟨a, ha⟩ := hf (1 / 2) (by simp)
  use a
  intro b hb
  replace ha := mem_Ioo.mp $ ha.right b (mem_Ici.mpr hb)
  linarith

lemma aux1 : ∃ h : ℕ → ℝ, h =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    (fun d ↦ (c + f d) ^ r) =ᶠ[atTop] (fun d ↦ c ^ (r + h d)) := by
  use fun d ↦ r * logb c (1 + (f d / c)), ?_, ?_
  · rw [isLittleO_one_iff] at hf hg ⊢
    simpa using (((hf.div_const c).const_add 1).logb (by simp) c).const_mul r
  · obtain ⟨a, ha⟩ := useful_aux hf
    simp only [EventuallyEq, eventually_atTop, ge_iff_le]
    use a
    intro b hb
    have : 0 < 1 + f b / c := by
      specialize ha b hb
      have : -1 / c < f b / c := by gcongr; linarith
      have : -1 < -1 / c := by rwa [neg_div, neg_lt_neg_iff, div_lt_iff (by linarith), one_mul]
      linarith
    rw [← mul_one_add, mul_comm r, rpow_mul (by linarith), ← logb_self_eq_one hc,
      ← logb_mul, rpow_logb _ _ _, logb_self_eq_one hc, mul_one_add, mul_div_cancel₀]
    all_goals try linarith
    · simp [logb_self_eq_one hc]
      exact mul_pos (by linarith) this
    · specialize ha b hb
      simp [logb_self_eq_one hc, this.ne.symm]

lemma aux2 : ∃ h : ℕ → ℝ, h =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    (fun d ↦ (c + f d) ^ (g d)) =ᶠ[atTop] (fun d ↦ c ^ h d) := by
  use fun d ↦ g d * logb c (c + f d), ?_, ?_
  · rw [isLittleO_one_iff] at hf hg ⊢
    simpa using Tendsto.mul hg $ (hf.const_add c).logb (by linarith) c
  · obtain ⟨a, ha⟩ := useful_aux hf
    simp only [EventuallyEq, eventually_atTop, ge_iff_le]
    use a
    intro b hb
    rw [mul_comm, rpow_mul, rpow_logb ?_ hc.ne.symm ?_]
    all_goals linarith [ha b hb]

/- Step 1: (c + o(1)) ^ (k + o(1)) = c ^ (k + o(1)) -/
lemma step1 : ∃ h : ℕ → ℝ, h =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    (fun d ↦ (c + f d) ^ (r + g d)) =ᶠ[atTop] (fun d ↦ c ^ (r + h d)) := by
  /- (1+o(1))^(r+o(1)) = c^(r+o(1)) -/
  obtain ⟨a, ha⟩ := useful_aux hf
  obtain ⟨l₁, hl₁⟩ := aux1 hc r hf
  obtain ⟨l₂, hl₂⟩ := aux2 hc hf hg
  use l₁ + l₂, by simpa using hl₁.left.add hl₂.left
  trans (fun d ↦ (c + f d) ^ r * (c + f d) ^ (g d))
  · rw [EventuallyEq, eventually_atTop]
    use a, fun b hb ↦ rpow_add (by linarith [ha b hb]) _ _
  refine (hl₁.right.mul hl₂.right).trans ?_
  simp only [EventuallyEq, eventually_atTop, Pi.add_apply]
  use 0, fun b _ ↦ by repeat rw [rpow_add] <;> try linarith


