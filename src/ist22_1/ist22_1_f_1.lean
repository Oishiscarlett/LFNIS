import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem ist22_1_f_1 (x₁ x₂ : ℝ)
                    (h₁ : f₁ = (x₁-1.2)*(5-x₁))
                    (h₂ : f₂ = (x₂-2.2)*(5-x₂))
                    (h₃ : I = (7369*x₁)/865 - (2621*x₂)/173 - (35214*x₁^2*x₂^2)/865 - (2291*x₁*x₂)/865
                     - (15126*x₁*x₂^2)/865 + (4259*x₁^2*x₂)/173 + (25786*x₁*x₂^3)/865 + (17799*x₁^3*x₂)/865
                      - (3316*x₁^2)/865 - (11312*x₁^3)/865 + (30118*x₂^2)/865 - (792*x₁^4)/865 - (18863*x₂^3)/865 - (877*x₂^4)/865 - 3336/865) :
                    0 ≤ f₁ → 0 ≤ f₂ → 0 < I := by

  let p₀ : ℝ :=(10714519181*x₁*x₂)/198673200 - (21647289421*x₂)/69535620 - (8059995253*x₁)/139071240 - (3548516219*x₁^2)/208606860 + (1645311737*x₂^2)/38630900 + 4954638948073/11589270000
  let p₁ : ℝ :=(106221263102548602060223*x₂)/2583929183478028951950 - (1011496349100889231114823*x₁)/20671433467824231615600 - (28515675625933715745623*x₁*x₂)/5167858366956057903900 + (982416935682861358279609*x₁^2)/62014300403472694846800 - (1341154016212686201217*x₂^2)/172261945565201930130
  let p₂ : ℝ :=(14681858334031253346344123946559441*x₁)/506479637967006214243946306966400 - (373028321598922056565420844973803*x₁*x₂)/26858768680068511361421395066400 + (160027211400161695285961527975453*x₁^2)/3545357465769043499707624148764800 + (74952889793134432345474676826409*x₂^2)/147723227740376812487817672865200
  let p₃ : ℝ :=(15156895751244059134280735660914362568192529*x₁^2)/35731924270316060528528968719330015887594700 - (27013604158384950704400967200966154797612233*x₁*x₂)/35731924270316060528528968719330015887594700 + (76538407756526664056126800120932485988719*x₂^2)/270696395987242882791886126661591029451475
  let p₄ : ℝ :=(120213000227702033098913178183312136992366620479351*x₁*x₂)/292718010043958984742097051476381346525178876892900 - (26661799904270118976810697378561472352722955094879*x₁^2)/48786335007326497457016175246063557754196479482150
  let p₅ : ℝ :=(260923568289891627216242159983319227647736073686461196903*x₁^2)/11145447337191202729057932228196110799052197629781825310160

  let p₀' : ℝ := (1401*x₁)/77 - (23789*x₂)/616 + 15355/308
  let p₁' : ℝ := (37105039*x₂)/18917360 - (10256417*x₁)/4729340
  let p₂' : ℝ := (263799083*x₁)/5714176006

  let p0 : ℝ := 1046/87 - (682*x₂)/261 - (799*x₁)/522
  let p1 : ℝ := (2643415*x₂)/409509 - (8042147*x₁)/819018
  let p2 : ℝ := (9889665583*x₁)/5519450520

  let σ₀ : ℝ := 11589270000/4954638948073*p₀^2 +
    2583929183478028951950/106221263102548602060223*p₁^2 +
    506479637967006214243946306966400/14681858334031253346344123946559441*p₂^2 +
    270696395987242882791886126661591029451475/76538407756526664056126800120932485988719*p₃^2 +
    292718010043958984742097051476381346525178876892900/120213000227702033098913178183312136992366620479351*p₄^2 +
    11145447337191202729057932228196110799052197629781825310160/260923568289891627216242159983319227647736073686461196903*p₅^2
  let σ₁ : ℝ := 308/15355*p₀'^2 + 18917360/37105039*p₁'^2 + 5714176006/263799083*p₂'^2
  let σ₂ : ℝ := 87/1046*p0^2 +  409509/2643415*p1^2 +  5519450520/9889665583*p2^2
  let ε : ℝ := 1/10000
  have h1 :11589270000/4954638948073*p₀^2 +
    2583929183478028951950/106221263102548602060223*p₁^2 +
    506479637967006214243946306966400/14681858334031253346344123946559441*p₂^2 +
    270696395987242882791886126661591029451475/76538407756526664056126800120932485988719*p₃^2 +
    292718010043958984742097051476381346525178876892900/120213000227702033098913178183312136992366620479351*p₄^2 +
    11145447337191202729057932228196110799052197629781825310160/260923568289891627216242159983319227647736073686461196903*p₅^2 = σ₀ :=by exact rfl
  have h2 : 308/15355*p₀'^2 + 18917360/37105039*p₁'^2 + 5714176006/263799083*p₂'^2= σ₁ := by exact rfl
  have h3 : 87/1046*p0^2 +  409509/2643415*p1^2 +  5519450520/9889665583*p2^2 = σ₂ := by exact rfl
  have I₁ : I = σ₀ + σ₁*f₁ + σ₂*f₂ + ε := by
    simp [h₁, h₂, h₃]
    linear_combination
  intro f1 f2
  have h1 : 0 ≤ σ₀ := by
    rw [← h1]
    have : 0 ≤ p₀^2 := by apply pow_two_nonneg
    have : 0 ≤ p₁^2 := by apply pow_two_nonneg
    have : 0 ≤ p₂^2 := by apply pow_two_nonneg
    have : 0 ≤ p₃^2 := by apply pow_two_nonneg
    have : 0 ≤ p₄^2 := by apply pow_two_nonneg
    have : 0 ≤ p₅^2 := by apply pow_two_nonneg
    linarith
  have h2 : 0 ≤ σ₁*f₁ := by
    have : 0 ≤ σ₁ := by
      rw [← h2]
      have : 0 ≤ p₀' ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ p₁' ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ p₂'^2 := by apply pow_two_nonneg
      linarith
    exact Right.mul_nonneg this f1
  have h3 : 0 ≤ σ₂*f₂ := by
    have : 0 ≤ σ₂ := by
      rw [← h3]
      have : 0 ≤ p0 ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ p1 ^ 2 := by apply pow_two_nonneg
      have : 0 ≤ p2 ^ 2 := by apply pow_two_nonneg
      linarith
    exact Right.mul_nonneg this f2
  have h4 : 0 < ε := by norm_num
  linarith
