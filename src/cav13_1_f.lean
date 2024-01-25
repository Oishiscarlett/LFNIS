import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem cav_13_1_f (x₁ x₂ : ℝ )
                   (h₁ : f₁ = x₁^2 - 2 * x₂^2 - 4)
                   (h₂ : I = x₁/5 - (3*x₂)/2 + (x₁*x₂)/10 + (9*x₁^2)/10 - (9*x₂^2)/10 - 1/2) :
                   0 ≤ f₁ → 0 ≤ I := by
  let p₀ : ℝ := x₁/10 - (3*x₂)/4 + 27/10
  let p₁ : ℝ := (7*x₁)/90 + (59*x₂)/120
  let p₂ : ℝ := (223*x₁)/2655
  let σ₀ : ℝ := 10/27*p₀^2 + 120/59*p₁^2 + 2655/223*p₂^2
  let σ₁ : ℝ := 4/5
  have I₁ : I = σ₀ + σ₁*f₁ - 0 := by
    simp [h₁, h₂]
    linear_combination
  intro f
  rw [I₁]
  have h1 : 0 ≤ σ₀ := by
    have : 0 ≤ 10 / 27 * (x₁ / 10 - 3 * x₂ / 4 + 27 / 10) ^ 2 := by
      have : 0 ≤ (x₁ / 10 - 3 * x₂ / 4 + 27 / 10) ^ 2 := by apply pow_two_nonneg
      linarith
    have : 0 ≤ 120 / 59 * (7 * x₁ / 90 + 59 * x₂ / 120) ^ 2 := by
      have : 0 ≤ (7 * x₁ / 90 + 59 * x₂ / 120) ^ 2 := by apply pow_two_nonneg
      linarith
    have : 0 ≤ 2655 / 223 * ((223 * x₁) ^ 2 / 2655 ^ 2) := by
      rw [←div_pow]
      have : 0 ≤ (223 * x₁ / 2655) ^ 2 := by apply pow_two_nonneg
      linarith
    simp
    linarith
  have h2 : 0 ≤ σ₁*f₁ := by simp; linarith
  linarith
