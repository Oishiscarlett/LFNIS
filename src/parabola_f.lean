-- import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem parabola_f (x₁ x₂ : ℝ)
                   (h₁ : f₁ = x₁^2 - x₂)
                   (h₂ : I = (3*x₁^2)/5 - (3*x₂)/5 + 3/10)
   : 0 ≤ f₁ → I > 0 := by
  let σ₀ : ℝ := 3/10-1/10000
  let σ₁ : ℝ := 3/5
  let ε : ℝ := 1/10000
  have I₁ : I = σ₀ + σ₁*f₁ + ε := by
    rw [h₂, h₁]
    simp
    rw [add_comm, add_assoc, sub_add]
    congr
    simp
    rw [←mul_div, ←mul_div, ←mul_sub, div_sub_div_same, mul_div, mul_div_right_comm]
  intro h1
  have h2 : 0 ≤ σ₀ := by simp; linarith
  have h3 : 0 ≤ σ₁ := by simp; linarith
  have h4 : 0 ≤ σ₁*f₁ := by simp; linarith
  rw [I₁]
  linarith
