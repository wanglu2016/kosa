-- 本文件由 Kosa 自動生成（kosa/lean.py），請勿手改。
-- 每一段 example 檢驗：某條目的 Lean 證明，只用到它的「依」所列的條目。
-- 若證明用了「依」以外的條目，assumption 找不到它，這裡就會報錯。

import Kosa.Proof4
import Kosa.Proof5
import Kosa.Proof6

namespace Kosa.Lib

example (W : «世界») (_O : «本體公理» W)  : «界品13» W := by
  apply «界品13成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «界品6» W) (h2 : «界品9» W) (h3 : «界品10» W) : «界品14» W := by
  apply «界品14成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «根品1» W) : «根品14» W := by
  apply «根品14成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «根品14» W) (h2 : «業品3» W) (h3 : «業品7» W) (h4 : «業品8» W) (h5 : «業品9» W) : «根品15» W := by
  apply «根品15成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品2» W) (h2 : «界品6» W) : «世間品6» W := by
  apply «世間品6成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品6» W) (h2 : «世間品1» W) : «世間品7» W := by
  apply «世間品7成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品7» W) (h2 : «界品13» W) : «世間品8» W := by
  apply «世間品8成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品7» W) (h2 : «界品7» W) (h3 : «界品8» W) (h4 : «世間品2» W) : «世間品9» W := by
  apply «世間品9成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品2» W) (h2 : «根品15» W) (h3 : «界品6» W) : «世間品10» W := by
  apply «世間品10成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品7» W) (h2 : «根品4» W) (h3 : «世間品1» W) : «世間品11» W := by
  apply «世間品11成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «世間品2» W) (h2 : «世間品3» W) (h3 : «世間品4» W) (h4 : «世間品7» W) (h5 : «世間品9» W) : «世間品12» W := by
  apply «世間品12成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品3» W) (h2 : «業品4» W) (h3 : «業品5» W) : «業品18» W := by
  apply «業品18成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品18» W) (h2 : «業品6» W) : «業品19» W := by
  apply «業品19成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品19» W) (h2 : «業品10» W) : «業品20» W := by
  apply «業品20成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品18» W) (h2 : «業品11» W) (h3 : «業品13» W) (h4 : «隨眠品6» W) (h5 : «業品16» W) : «業品21» W := by
  apply «業品21成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品12» W) (h2 : «業品14» W) (h3 : «界品11» W) (h4 : «業品13» W) (h5 : «業品15» W) (h6 : «界品1» W) : «業品22» W := by
  apply «業品22成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品18» W) (h2 : «業品11» W) (h3 : «業品14» W) (h4 : «界品11» W) (h5 : «業品13» W) (h6 : «業品15» W) (h7 : «界品1» W) : «業品23» W := by
  apply «業品23成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品21» W) (h2 : «業品23» W) : «業品24» W := by
  apply «業品24成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «業品20» W) (h2 : «業品24» W) : «業品25» W := by
  apply «業品25成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «隨眠品2» W) (h2 : «隨眠品3» W) : «隨眠品5» W := by
  apply «隨眠品5成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «根品2» W) (h2 : «根品15» W) (h3 : «根品3» W) (h4 : «隨眠品1» W) (h5 : «隨眠品5» W) (h6 : «隨眠品4» W) : «隨眠品6» W := by
  apply «隨眠品6成立» W <;> assumption

end Kosa.Lib

namespace Kosa.LibP

example (W : «世界») (_O : «本體公理» W) (h1 : «賢聖品4» W) (h2 : «定品2» W) : «賢聖品6» W := by
  apply «賢聖品6成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «賢聖品3» W) (h2 : «智品2» W) (h3 : «智品3» W) (h4 : «智品4» W) : «智品5» W := by
  apply «智品5成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «賢聖品3» W) (h2 : «定品4» W) (h3 : «定品5» W) : «定品9» W := by
  apply «定品9成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «定品3» W) (h2 : «智品1» W) (h3 : «智品2» W) (h4 : «智品3» W) (h5 : «賢聖品2» W) : «定品10» W := by
  apply «定品10成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «定品3» W) (h2 : «定品6» W) (h3 : «定品7» W) (h4 : «賢聖品5» W) (h5 : «定品1» W) : «定品11» W := by
  apply «定品11成立» W <;> assumption

example (W : «世界») (_O : «本體公理» W) (h1 : «定品9» W) (h2 : «定品10» W) (h3 : «定品1» W) : «定品12» W := by
  apply «定品12成立» W <;> assumption

end Kosa.LibP
