import Mathlib.Tactic


theorem cav20_4_4 (x₁ x₂ x₅ x₆: ℝ)
            (h₁ : g₃=16-(x₁+x₂+4)^2-16*(x₁-x₂)^2-x₅^2)
            (h₂ : g₄=-x₁-x₂-x₆^2-(2-x₆)^2)
            (h₃ : I = (3*x₁)/100 + (2*x₂)/25 - (103*x₁*x₂)/50 - (3*x₁^2)/100 - x₂^2/50 + 91/100)
              :
              0 ≤ g₃ ∧ 0 ≤ g₄
              → I ≤ 0 := by
  let p₀: ℝ :=(81*x₁)/200 + (2*x₂)/5 - (19*x₆)/50 - (109*x₁*x₂)/400 + (19*x₁*x₆)/400 + (17*x₂*x₆)/400 + (7*x₁^2)/30 + (23*x₂^2)/100 + (7*x₅^2)/300 + x₆^2/10 + 69/100
  let p₁: ℝ :=(24719*x₁)/27600 + (1313*x₂)/9200 + (2213*x₆)/9200 - (127*x₁*x₂)/736 - (719*x₁*x₆)/3680 + (14171*x₂*x₆)/55200 + (559*x₁^2)/2300 + (61*x₂^2)/400 + (167*x₅^2)/4600 + (1553*x₆^2)/9200
  let p₂: ℝ :=(5252533*x₂)/5932560 + (3032413*x₆)/14831400 - (8722777*x₁*x₂)/59325600 + (5443411*x₁*x₆)/19775200 - (13380679*x₂*x₆)/59325600 + (10100633*x₁^2)/88988400 + (6595987*x₂^2)/29662800 + (1365451*x₅^2)/44494200 + (2041243*x₆^2)/14831400
  let p₃: ℝ :=(6291527377*x₆)/10505066000 + (28482978593*x₁*x₂)/63030396000 + (3943670023*x₁*x₆)/63030396000 + (79258809*x₂*x₆)/1616164000 - (2001063693*x₁^2)/10505066000 - (2055236351*x₂^2)/10505066000 - (20942751*x₅^2)/5252533000 - (4118485983*x₆^2)/10505066000
  let p₄: ℝ :=(6264144102127*x₁*x₆)/22649498557200 - (3536696325203*x₁*x₂)/7549832852400 - (197585913867*x₂*x₆)/1258305475400 + (1736475256231*x₁^2)/3774916426200 + (18924384454*x₂^2)/471864553275 - (5558203097*x₅^2)/1887458213100 + (12434152243*x₆^2)/503322190160
  let p₅: ℝ :=(393801971040879*x₂*x₆)/1389180204984800 - (2161365302840911*x₁*x₆)/12502621844863200 - (1768692086867387*x₁*x₂)/4167540614954400 + (946264778164711*x₂^2)/2083770307477200 - (2826319586741*x₅^2)/1041885153738600 + (1004306314407*x₆^2)/43411881405775
  let p₆: ℝ :=(61623501473329*x₁*x₆)/11355177337976532 - (12740150976328529*x₁*x₂)/1135517733797653200 + (849530886973287*x₂*x₆)/189252955632942200 + (62586244761661*x₅^2)/9462647781647110 - (4149388570009849*x₆^2)/567758866898826600
  let p₇: ℝ :=(35175243922584079*x₁*x₆)/450620962283959200 - (112363029991298081*x₁*x₂)/4506209622839592000 + (17917021261689731*x₂*x₆)/250344979046644000 + (138046861515433571*x₆^2)/563276202854949000
  let p₈: ℝ :=(930489354989037897427*x₁*x₂)/15902998446577947379200 + (312901831748871278231*x₁*x₆)/7951499223288973689600 + (30219053815592323267*x₂*x₆)/883499913698774854400
  let p₉: ℝ :=(4030221418400464907365517*x₁*x₆)/13399046711842145722948800 - (1201807011225452518967461*x₂*x₆)/4466348903947381907649600
  let p₁₀: ℝ :=(81128920383258763952080147*x₂*x₆)/1209066425520139472209655100
  let p₁₁: ℝ :=x₅/3 + (x₁*x₅)/25 + (x₂*x₅)/25 - (9*x₅*x₆)/50
  let p₁₂: ℝ :=(291*x₁*x₅)/10000 + (291*x₂*x₅)/10000 + (257*x₅*x₆)/2500
  let p₁₃: ℝ :=(64543*x₂*x₅)/411200 - (58817*x₁*x₅)/411200
  let p₁₄: ℝ :=(8589*x₁*x₅)/322715
  let p₀': ℝ :=x₁/100 + x₂/100 - x₆/50 + 3/50
  let p₁': ℝ :=(23*x₁)/600 - (7*x₂)/600 + (11*x₆)/600
  let p₂': ℝ :=(4*x₂)/115 + (11*x₆)/460
  let p₃': ℝ :=(9*x₆)/320
  let p₄': ℝ :=x₅/100
  let p0: ℝ :=(21*x₆)/200 - x₁/200 + 2/5
  let p1: ℝ :=(1599*x₁)/16000 - (9*x₂)/200 + (421*x₆)/16000
  let p2: ℝ :=(85*x₂)/1066 + (4461*x₆)/106600
  let p3: ℝ :=(1191089*x₆)/5100000
  let p4: ℝ :=(2*x₅)/25
  let δ₀₂: ℝ :=100/69*(p₀^2) + 27600/24719*(p₁^2) +  5932560/5252533*(p₂^2) + 10505066000/6291527377*(p₃^2) + 3774916426200/1736475256231*(p₄^2) +
      2083770307477200/946264778164711*(p₅^2) + 9462647781647110/62586244761661*(p₆^2) + 563276202854949000/138046861515433571*(p₇^2) + 15902998446577947379200/930489354989037897427*(p₈^2) +
      13399046711842145722948800/4030221418400464907365517*(p₉^2) + 1209066425520139472209655100/81128920383258763952080147*(p₁₀^2) + 3*(p₁₁^2) +
      2500/257*(p₁₂^2) + 411200/64543*(p₁₃^2) + 322715/8589*(p₁₄^2)
  let δ₂₁: ℝ :=50/3*(p₀'^2) +600/23*(p₁'^2) +115/4*(p₂'^2) +320/9*(p₃'^2) +100*(p₄'^2)
  let δ₂₂: ℝ :=5/2*(p0^2) +16000/1599*(p1^2) +1066/85*(p2^2) +5100000/1191089*(p3^2) +25/2*(p4^2)
  have h1 :100/69*(p₀^2) + 27600/24719*(p₁^2) +  5932560/5252533*(p₂^2) + 10505066000/6291527377*(p₃^2) + 3774916426200/1736475256231*(p₄^2) +
      2083770307477200/946264778164711*(p₅^2) + 9462647781647110/62586244761661*(p₆^2) + 563276202854949000/138046861515433571*(p₇^2) + 15902998446577947379200/930489354989037897427*(p₈^2) +
      13399046711842145722948800/4030221418400464907365517*(p₉^2) + 1209066425520139472209655100/81128920383258763952080147*(p₁₀^2) + 3*(p₁₁^2) +
      2500/257*(p₁₂^2) + 411200/64543*(p₁₃^2) + 322715/8589*(p₁₄^2)= δ₀₂ := by exact rfl
  have h2 : 50/3*(p₀'^2) +600/23*(p₁'^2) +115/4*(p₂'^2) +320/9*(p₃'^2) +100*(p₄'^2)= δ₂₁ := by  exact rfl
  have h3 :5/2*(p0^2) +16000/1599*(p1^2) +1066/85*(p2^2) +5100000/1191089*(p3^2) +25/2*(p4^2)= δ₂₂ := by  exact rfl
  have D₁: I = -δ₀₂ - δ₂₁*g₃- δ₂₂*g₄:= by
    rw  [h₁,h₂,h₃]
    linear_combination
  have l₀ : δ₀₂ ≥ 0 := by
    rw [← h1]
    have : p₀ ^ 2 ≥ 0 := by
      exact sq_nonneg p₀
    have : p₁ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁
    have : p₂ ^ 2  ≥ 0 := by
      exact sq_nonneg p₂
    have : p₃ ^ 2  ≥ 0 := by
      exact sq_nonneg p₃
    have : p₄ ^ 2 ≥ 0 := by
      exact sq_nonneg p₄
    have : p₅ ^ 2 ≥ 0 := by
      exact sq_nonneg p₅
    have : p₆ ^ 2 ≥ 0 := by
      exact sq_nonneg p₆
    have : p₇ ^ 2 ≥ 0 := by
      exact sq_nonneg p₇
    have : p₈ ^ 2 ≥ 0 := by
      exact sq_nonneg p₈
    have : p₉ ^ 2 ≥ 0 := by
      exact sq_nonneg p₉
    have : p₁₀ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁₀
    have : p₁₁ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁₁
    have : p₁₂ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁₂
    have : p₁₃ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁₃
    have : p₁₄ ^ 2 ≥ 0 := by
      exact sq_nonneg p₁₄
    linarith
  have l₁: 0 ≤ δ₂₁ := by
    rw [← h2]
    have : p₀' ^ 2 ≥ 0 := by
      exact sq_nonneg p₀'
    have : p₁' ^ 2 ≥ 0 := by
      exact sq_nonneg p₁'
    have : p₂' ^ 2 ≥ 0 := by
      exact sq_nonneg p₂'
    have : p₃' ^ 2 ≥ 0 := by
      exact sq_nonneg p₃'
    have : p₄' ^ 2 ≥ 0 := by
      exact sq_nonneg p₄'
    linarith
  have l₂: 0 ≤ δ₂₂ := by
    rw [← h3]
    have : p0 ^ 2 ≥ 0 := by
        exact sq_nonneg p0
    have : p1 ^ 2  ≥ 0 := by
        exact sq_nonneg p1
    have : p2 ^ 2  ≥ 0 := by
        exact sq_nonneg p2
    have : p3 ^ 2 ≥ 0 := by
        exact sq_nonneg p3
    have : p4 ^ 2 ≥ 0 := by
        exact sq_nonneg p4
    linarith
  rw [D₁]
  intro g
  have s₁ : 0 ≤ δ₂₁*g₃ := by
    exact Right.mul_nonneg l₁ g.left
  have s₂ : 0 ≤ δ₂₂*g₄  := by
    exact Right.mul_nonneg l₂ g.right
  linarith
