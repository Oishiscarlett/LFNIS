import Mathlib.Tactic  ---在数学库（Mathlib）中用于处理自动证明的策略（tactic）的文件
-- import Mathlib.Order.Basic   --关于基本的排序理论的文件

import Mathlib.Tactic  ---在数学库（Mathlib）中用于处理自动证明的策略（tactic）的文件
import Mathlib.Order.Basic   --关于基本的排序理论的文件

theorem face2(x₁ x₂: ℝ)
             (h₁ : g₁=1 - (x₁ + 4)^2 - x₂^2)
             (h₂: I=(57*x₁)/1000 - (795737*x₂)/1000000 + (38891*x₁^2*x₂^2)/1000000 + (279129*x₁*x₂)/1000000 + (31191*x₁*x₂^2)/200000 + (22271*x₁^2*x₂)/250000 - (36391*x₁*x₂^3)/500000 - (1159*x₁^3*x₂)/62500 - (1061523*x₁^2)/1000000 - (12773*x₁^3)/1000000 + (76769*x₂^2)/20000 + (24401*x₁^4)/1000000 + (7737*x₂^3)/125000 + (436083*x₂^4)/500000 + 224497/100000):
              0 ≤ g₁
                →  I ≤  0 := by
  let p₀: ℝ :=(24621* x₁)/62500 + (446821*x₂)/1000000 + (113908955507549707057* x₁*x₂)/1125899906842624000000 - (272606692162506299063* x₁^2)/1688849860263936000000 - (310512995285266152503*x₂^2)/6755399441055744000000 + 218947/50000
  let p₁: ℝ :=(45859262571790766783065243897*x₂)/3697686103552079953920000000 - (805842479220730807157544991* x₁)/1232562034517359984640000000 + (17481962892031887452058194483* x₁*x₂)/4930248138069439938560000000 - (936138426579440733827608777* x₁^2)/7395372207104159907840000000 - (680205000403942552346842957*x₂^2)/29581488828416639631360000000
  let p₂: ℝ :=(896465683083066359904117433714038152163292280432021* x₁)/154898818372351973514041110695938825266397184000000 + (13799469277501069708574146834497618222067258581169* x₁*x₂)/206531757829802631352054814261251767021862912000000 + (28541669448747522552332490290332103175506489802059* x₁^2)/20653175782980263135205481426125176702186291200000 + (39644134250670375886842503432059134588405161055783*x₂^2)/82612703131921052540821925704500706808745164800000
  let p₃: ℝ :=(2553217163055398564232707932272574695899923088147385067958202264191069640112986027779* x₁*x₂)/214753750156395353817572003939371137708508811975523909914038578577353545720266752000000 - (2654719006197190082850693688497609931843315906306088147960335707913135991325949162549* x₁^2)/322130625234593030726358005909056706562763217963285864871057867866030318580400128000000 + (177424968778998542738327297890401464097283440048183075622208823977395822394245189382987*x₂^2)/1288522500938372122905432023636226826251052871853143459484231471464121274321600512000000
  let p₄: ℝ :=(41962239250609004050042421134991493721239873707852647121436873099350143213219461889051252130147179208270407* x₁*x₂)/297303163934981264400329631231842790104864312082628662375310486375597160308681892013058434483395493888000000 + (728567822562417782138647943543661294120597387991967185771457516675517728048371907375240142975645932092767* x₁^2)/99101054644993754800109877077280930034954770694209554125103495458532386769560630671019478161131831296000000
  let p₅: ℝ :=(1007508887180657773756273822457990604136020706203636599462185725981284310599788212037647910547850881180620400223500243692271* x₁^2)/553655639802756773308611828287839232320249645505732744520498925025928265585747794997842457702909348964882137465680297984000000
  let p₀': ℝ :=(6527*x₂)/2000000 - (22399* x₁)/250000 + 220797/500000
  let p₁': ℝ :=(1854966613199*x₂)/1766376000000 - (5726560333* x₁)/220797000000
  let p₂': ℝ :=(16022697186155511* x₁)/46374165329975000
  let δ₁₀: ℝ :=50000/218947  *(p₀^2)+
      3697686103552079953920000000/45859262571790766783065243897  *(p₁^2)+
      154898818372351973514041110695938825266397184000000/896465683083066359904117433714038152163292280432021  *(p₂^2)+
      1288522500938372122905432023636226826251052871853143459484231471464121274321600512000000/177424968778998542738327297890401464097283440048183075622208823977395822394245189382987  *(p₃^2)+
      297303163934981264400329631231842790104864312082628662375310486375597160308681892013058434483395493888000000/41962239250609004050042421134991493721239873707852647121436873099350143213219461889051252130147179208270407  *(p₄^2)+
      553655639802756773308611828287839232320249645505732744520498925025928265585747794997842457702909348964882137465680297984000000/1007508887180657773756273822457990604136020706203636599462185725981284310599788212037647910547850881180620400223500243692271*(p₅^2)
  let δ₁₁: ℝ :=500000/220797  *(p₀'^2) +
      1766376000000/1854966613199  *(p₁'^2) +
      46374165329975000/16022697186155511*(p₂'^2)
  have h0 :50000/218947  *(p₀^2)+
      3697686103552079953920000000/45859262571790766783065243897  *(p₁^2)+
      154898818372351973514041110695938825266397184000000/896465683083066359904117433714038152163292280432021  *(p₂^2)+
      1288522500938372122905432023636226826251052871853143459484231471464121274321600512000000/177424968778998542738327297890401464097283440048183075622208823977395822394245189382987  *(p₃^2)+
      297303163934981264400329631231842790104864312082628662375310486375597160308681892013058434483395493888000000/41962239250609004050042421134991493721239873707852647121436873099350143213219461889051252130147179208270407  *(p₄^2)+
      553655639802756773308611828287839232320249645505732744520498925025928265585747794997842457702909348964882137465680297984000000/1007508887180657773756273822457990604136020706203636599462185725981284310599788212037647910547850881180620400223500243692271*(p₅^2)
        = δ₁₀ := by exact rfl
  have h1 : 500000/220797  *(p₀'^2) +
      1766376000000/1854966613199  *(p₁'^2) +
      46374165329975000/16022697186155511*(p₂'^2) = δ₁₁ := by exact rfl
  have D₁: I =- δ₁₀ - δ₁₁*g₁ := by
    rw [h₁,h₂]
    linear_combination
--     linear_combination (2251799813685248/1443338378377647*(p₀'^2) +7517387387383578125000000/13288784152026326846058509*(p₁'^2) + 53155136608105307384234036000000/20920674620360211666579718264431*(p₂'^2))* h₁ +h₂+ h0 + g₁ * h1
  have l₀: δ₁₀ ≥ 0 := by
    rw [← h0]
    have : p₀ ^ 2 ≥ 0 := by --开始证明每一个平方和项大于等于0
          exact sq_nonneg p₀
    have : p₁ ^ 2 ≥ 0 := by
          exact sq_nonneg p₁
    have : p₂ ^ 2 ≥ 0 := by
          exact sq_nonneg p₂
    have : p₃ ^ 2 ≥ 0 := by
          exact sq_nonneg p₃
    have : p₄ ^ 2 ≥ 0 := by
          exact sq_nonneg p₄
    have : p₅ ^ 2 ≥ 0 := by
          exact sq_nonneg p₅
    linarith
  have l₁: δ₁₁ ≥ 0 := by
    rw [← h1]
    have : p₀' ^ 2 ≥ 0 := by
      exact sq_nonneg p₀' --应用策略sq_nonneg（x^ 2 ≥ 0)
    have : p₁' ^ 2 ≥ 0 := by
      exact sq_nonneg p₁'
    have : p₂' ^ 2 ≥ 0 := by
      exact sq_nonneg p₂'
    linarith
  rw [D₁]
  intro g
  have s₁ : 0 ≤ δ₁₁*g₁ := by
    exact Right.mul_nonneg l₁ g
  linarith