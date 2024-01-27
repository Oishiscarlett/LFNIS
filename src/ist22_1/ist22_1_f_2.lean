import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem ist22_1_f_2 (x₁ x₂ : ℝ)
                    (h₁ : f₃ = (2.2-x₂)*(x₂-1.2))
                    (h₂ : f₄ = (x₁-2.2)*(5-x₁))
                    (h₃ : I = (213*x₁)/25 - (303*x₂)/20 - (4071*x₁^2*x₂^2)/100 - (53*x₁*x₂)/20 - (1749*x₁*x₂^2)/100
                          + (1231*x₁^2*x₂)/50 + (2981*x₁*x₂^3)/100 + (1029*x₁^3*x₂)/50 - (383*x₁^2)/100
                          - (327*x₁^3)/25 + (1741*x₂^2)/50 - (91*x₁^4)/100 - (2181*x₂^3)/100 - (101*x₂^4)/100 - 193/50) :
                    0 ≤ f₃ → 0 ≤ f₄ → 0 < I := by
  let p₀ : ℝ := (2074*x₁*x₂)/125 - (71203*x₂)/1000 - (361049*x₁)/2500 + (1851*x₁^2)/100 + (22726*x₂^2)/1875 + 499811/2000
  let p₁ : ℝ := (200158745096*x₂)/937145625 - (13760756953*x₁)/96117500 + (11427872459*x₁*x₂)/499811000
                + (5425914139*x₁^2)/249905500 - (598645785947*x₂^2)/7497165000
  let p₂ : ℝ := (260261513003155459*x₁)/10007937254800000 - (112158653787733517*x₁*x₂)/4003174901920000
                - (716392811072473*x₁^2)/400317490192000 + (1121559213243637597*x₂^2)/60047623528800000
  let p₃ : ℝ := (2102987338250219933*x₁^2)/2602615130031554590 - (1572840973330584050789*x₁*x₂)/390392269504733188500
                + (17918630470041934142711*x₂^2)/4684707234056798262000
  let p₄ : ℝ := (28531674639380527699380823*x₁*x₂)/107511782820251604856266000 - (609651804118559307305199*x₁^2)/3583726094008386828542200
  let p₅ : ℝ := (25624125674265544421470241*x₁^2)/2853167463938052769938082300

  let p₆ : ℝ := (83*x₂)/8 - (4293*x₁)/200 + 651/25
  let p₇ : ℝ := (46409879*x₂)/1041600 - (2655927*x₁)/69440
  let p₈ : ℝ := (1734596929*x₁)/4640987900

  let p₉ : ℝ := 841/50 - (17*x₂)/4 - (143*x₁)/50
  let q₀ : ℝ := (1948787*x₂)/168200 - (275539*x₁)/42050
  let q₁ : ℝ := (34482824*x₁)/48719675

  let σ₀ : ℝ := 2000/499811*p₀^2 + 937145625/200158745096*p₁^2 + 10007937254800000/260261513003155459*p₂^2
                + 4684707234056798262000/17918630470041934142711*p₃^2 + 107511782820251604856266000/28531674639380527699380823*p₄^2
                + 2853167463938052769938082300/25624125674265544421470241*p₅^2
  let σ₁ : ℝ := 25/651*p₆^2 + 1041600/46409879*p₇^2 + 4640987900/1734596929*p₈^2
  let σ₂ : ℝ := 50/841*p₉^2 + 168200/1948787*q₀^2 + 48719675/34482824*q₁^2
  let ε : ℝ := 1/10000

  have I₁ : I = σ₀ + σ₁*f₃ + σ₂*f₄ + ε := by
    simp [h₁, h₂, h₃]
    linear_combination
  intro f3 f4
  rw [I₁]
  have h1 : 0 ≤ σ₀ := by
    have : 0 ≤ ((2074*x₁*x₂)/125 - (71203*x₂)/1000 - (361049*x₁)/2500 + (1851*x₁^2)/100 + (22726*x₂^2)/1875 + 499811/2000)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((200158745096*x₂)/937145625 - (13760756953*x₁)/96117500 + (11427872459*x₁*x₂)/499811000
                + (5425914139*x₁^2)/249905500 - (598645785947*x₂^2)/7497165000)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((260261513003155459*x₁)/10007937254800000 - (112158653787733517*x₁*x₂)/4003174901920000
                - (716392811072473*x₁^2)/400317490192000 + (1121559213243637597*x₂^2)/60047623528800000)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((2102987338250219933*x₁^2)/2602615130031554590 - (1572840973330584050789*x₁*x₂)/390392269504733188500
                + (17918630470041934142711*x₂^2)/4684707234056798262000)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((28531674639380527699380823*x₁*x₂)/107511782820251604856266000 - (609651804118559307305199*x₁^2)/3583726094008386828542200)^2 := by apply pow_two_nonneg
    have : 0 ≤ ((25624125674265544421470241 * x₁ ^ 2) ^ 2 / 2853167463938052769938082300 ^ 2) := by
      rw [←div_pow]
      have : 0 ≤ ((25624125674265544421470241*x₁^2)/2853167463938052769938082300) ^ 2 := by apply pow_two_nonneg
      linarith
    simp
    linarith
  have h2 : 0 ≤ σ₁*f₃ := by
    have : 0 ≤ σ₁ := by
      have : 0 ≤ ((83*x₂)/8 - (4293*x₁)/200 + 651/25) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((46409879*x₂)/1041600 - (2655927*x₁)/69440) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((1734596929 * x₁) ^ 2 / 4640987900 ^ 2) := by
        rw [←div_pow]
        have : 0 ≤ ((1734596929*x₁)/4640987900) ^ 2 := by apply pow_two_nonneg
        linarith
      simp
      linarith
    exact Right.mul_nonneg this f3
  have h3 : 0 ≤ σ₂*f₄ := by
    have : 0 ≤ σ₂ := by
      have : 0 ≤ (841/50 - (17*x₂)/4 - (143*x₁)/50) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((1948787*x₂)/168200 - (275539*x₁)/42050) ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ ((34482824 * x₁) ^ 2 / 48719675 ^ 2) := by
        rw [←div_pow]
        have : 0 ≤ ((34482824*x₁)/48719675) ^ 2 := by apply pow_two_nonneg
        linarith
      simp
      linarith
    exact Right.mul_nonneg this f4
  have h4 : 0 < ε := by norm_num
  linarith