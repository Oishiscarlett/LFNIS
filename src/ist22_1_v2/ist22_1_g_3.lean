import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem ist22_1_g_3 (x₁ x₂ : ℝ)
                    (h₁ : g₅ = (3-x₁)*(x₁-2))
                    (h₂ : g₆ = (1-x₂)*x₂)
                    (h₃ : I = (213*x₁)/25 - (303*x₂)/20 - (4071*x₁^2*x₂^2)/100 - (53*x₁*x₂)/20 - (1749*x₁*x₂^2)/100
                          + (1231*x₁^2*x₂)/50 + (2981*x₁*x₂^3)/100 + (1029*x₁^3*x₂)/50 - (383*x₁^2)/100
                          - (327*x₁^3)/25 + (1741*x₂^2)/50 - (91*x₁^4)/100 - (2181*x₂^3)/100 - (101*x₂^4)/100 - 193/50) :
                    0 ≤ g₅ → 0 ≤ g₆ → 0 ≤ -I := by
  let p₀ : ℝ := (397*x₁^2)/100 - (621*x₂)/200 - (9*x₁*x₂)/50 - (4321*x₁)/200 - (71*x₂^2)/150 + 797/25
  let p₁ : ℝ := (63138661*x₂)/3825600 - (205269*x₁)/51008 - (681437*x₁*x₂)/63760 + (1603031*x₁^2)/637600 + (1447001*x₂^2)/318800
  let p₂ : ℝ := (69876219471*x₁)/6313866100 - (409907276593*x₁*x₂)/25255464400 + (49210048991*x₁^2)/25255464400 + (23334089899*x₂^2)/37883196600
  let p₃ : ℝ := (338044772662423*x₁^2)/167702926730400 - (1532827351953761*x₁*x₂)/167702926730400 + (2540807678929487*x₂^2)/251554390095600
  let p₄ : ℝ := (46316748448166948083*x₁*x₂)/3048969214715384400 - (5684153748880815603*x₁^2)/1016323071571794800
  let p₅ : ℝ := (9454028425822476243*x₁^2)/1157918711204173702075

  let p₆ : ℝ := 467/100 - (131*x₂)/100 - (189*x₁)/200
  let p₇ : ℝ := (31581*x₂)/4670 - (44367*x₁)/23350
  let p₈ : ℝ := (14421301*x₁)/7018000

  let p₉ : ℝ := (33*x₁)/200 - (113*x₂)/100 + 141/25
  let q₀ : ℝ := (73623*x₁)/37600 + (572663*x₂)/56400
  let q₁ : ℝ := (131455633*x₁)/11453260

  let δ₀ : ℝ := 25/797*p₀^2 + 3825600/63138661*p₁^2 + 6313866100/69876219471*p₂^2 + 251554390095600/2540807678929487*p₃^2
                + 3048969214715384400/46316748448166948083*p₄^2 + 1157918711204173702075/9454028425822476243*p₅^2
  let δ₁ : ℝ := 100/467*p₆^2 + 4670/31581*p₇^2 + 7018000/14421301*p₈^2
  let δ₂ : ℝ := 25/141*p₉^2 + 56400/572663*q₀^2 + 11453260/131455633*q₁^2

  have I₁ : -I = δ₀ + δ₁*g₅ + δ₂*g₆ := by
    simp [h₁, h₂, h₃]
    linear_combination
  intro g5 g6
  rw [I₁]
  have h1 : 0 ≤ δ₀ := by
    have : 0 ≤ ((397*x₁^2)/100 - (621*x₂)/200 - (9*x₁*x₂)/50 - (4321*x₁)/200 - (71*x₂^2)/150 + 797/25)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((63138661*x₂)/3825600 - (205269*x₁)/51008 - (681437*x₁*x₂)/63760 + (1603031*x₁^2)/637600 + (1447001*x₂^2)/318800)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((69876219471*x₁)/6313866100 - (409907276593*x₁*x₂)/25255464400 + (49210048991*x₁^2)/25255464400 + (23334089899*x₂^2)/37883196600)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((338044772662423*x₁^2)/167702926730400 - (1532827351953761*x₁*x₂)/167702926730400 + (2540807678929487*x₂^2)/251554390095600)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((46316748448166948083*x₁*x₂)/3048969214715384400 - (5684153748880815603*x₁^2)/1016323071571794800)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((9454028425822476243*x₁^2)^2/1157918711204173702075^2) := by
      rw [←div_pow]
      have : 0 ≤ ((9454028425822476243*x₁^2)/1157918711204173702075) ^ 2 := by apply pow_two_nonneg
      linarith
    simp
    linarith
  have h2 : 0 ≤ δ₁*g₅ := by
    have : 0 ≤ δ₁ := by
      have : 0 ≤ (467/100 - (131*x₂)/100 - (189*x₁)/200) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((31581*x₂)/4670 - (44367*x₁)/23350) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((14421301*x₁)^2/7018000^2) := by
        rw [←div_pow]
        have : 0 ≤ ((14421301*x₁)/7018000) ^ 2 := by apply pow_two_nonneg
        linarith
      simp
      linarith
    exact Right.mul_nonneg this g5
  have h3 : 0 ≤ δ₂*g₆ := by
    have : 0 ≤ δ₂ := by
      have : 0 ≤ ((33*x₁)/200 - (113*x₂)/100 + 141/25) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((73623*x₁)/37600 + (572663*x₂)/56400) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((131455633*x₁)^2/11453260^2) := by
        rw [←div_pow]
        have : 0 ≤ ((131455633*x₁)/11453260) ^ 2 := by apply pow_two_nonneg
        linarith
      simp
      linarith
    exact Right.mul_nonneg this g6
  linarith
