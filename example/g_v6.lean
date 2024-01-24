import Mathlib.Tactic  ---在数学库（Mathlib）中用于处理自动证明的策略（tactic）的文件
-- import Mathlib.Order.Basic   --关于基本的排序理论的文件

theorem exp2 (x₁ x₂ y: ℝ)
            (h₁ : g₁=-x₁^2 + 4*x₁ + x₂ - 4)
            (h₂ : g₂ = -y^2 - x₁- x₂ + 3)
            (h₃ : I = 107/50*x₂ - 2881/1000*x₁ - 2479/1000*x₁*x₂ - 327/500*x₁^2 - 147/125*x₂^2 + 581/200)
              :
              0 ≤ g₁ ∧ 0 ≤ g₂
              → I ≤ 0 := by
  let p₁: ℝ := 2197/500 - (19*x₂)/10 - (717*x₁)/250
  let p₂: ℝ := (2418969*x₁)/2197000 -(2837*x₂)/4394000
  let p₃: ℝ := (3429369899*x₂)/9675876000
  let p₄: ℝ := (659*y)/1000
  let δ₀: ℝ := 500/2197*(p₁^2) + 2197000/2418969*(p₂^2) + 9675876000/3429369899*(p₃^2) + 1000/659*(p₄^2)
  let δ₁: ℝ := 2319/1000
  let δ₂: ℝ := 659/1000
  have h1 :500/2197*(p₁^2) + 2197000/2418969*(p₂^2) + 9675876000/3429369899*(p₃^2) + 1000/659*(p₄^2)= δ₀ := by exact rfl
  have h2 : 2319/1000= δ₁ := by  exact rfl
  have h3 : 659/1000= δ₂ := by  exact rfl
  have I₁: I = -δ₀ - δ₁*g₁- δ₂*g₂  := by
    linear_combination 2319 / 1000 * h₁ + 659 / 1000 * h₂ + h₃ + h1 + g₁ * h2 + g₂ * h3
  have l₀ : δ₀ ≥ 0 := by
    rw [← h1]
    have : p₁ ^ 2 ≥ 0 := by --分别证明每一个平方和项大于等于0
      exact sq_nonneg p₁   --应用策略sq_nonneg（x^ 2 ≥ 0)
    have : p₂ ^ 2  ≥ 0 := by
        exact sq_nonneg p₂
    have : p₃ ^ 2  ≥ 0 := by
      exact sq_nonneg p₃
    have : p₄ ^ 2 ≥ 0 := by
      exact sq_nonneg p₄
    linarith
  have l₁: 0 ≤ δ₁ := by
    rw [← h2]
    linarith
  have l₂: 0 ≤ δ₂ := by
    rw [← h3]
    linarith
  rw [I₁]
  intro g
  have s₁ : 0 ≤ δ₁*g₁ := by
    exact Right.mul_nonneg l₁ g.left
  have s₂ : 0 ≤ δ₂*g₂  := by
    exact Right.mul_nonneg l₂ g.right
  linarith
