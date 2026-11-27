import Kosa.Lib

/-!
# 模組六的證明：阿那含必然成就初靜慮

論域是補特伽羅。`W.«果位» p = .«不還»` 讀作「p 是不還（阿那含）」，
`W.«成就淨初靜慮» p` 讀作「p 成就淨初靜慮」。

注意：目標所依的假定中，智品2（先離欲染、依未至入見道而證不還者成就無漏初靜慮）
狀態是「待核」。Lean 證明的是「若這些假定成立，則目標成立」；假定本身的真假，Lean 不管。
-/

namespace Kosa.Lib

/-- 不還是聖者（不是異生）。 -/
theorem «不還是聖者» (W : «世界») (p : W.«有情») (h : W.«果位» p = .«不還») : «聖者» W p := by
  intro hYi
  rw [h] at hYi
  cases hYi

/-- 【定品9】生在欲界或初靜慮的不還，成就淨初靜慮。依：賢聖品3、定品4、定品5。 -/
theorem «定品9成立» (W : «世界») (a1 : «賢聖品3» W) (a5 : «定品4» W) (a6 : «定品5» W) :
    «定品9» W := by
  intro p ⟨hBu, hNot⟩
  cases h : W.«生地» p
  case «生欲界» => exact a5 p ⟨h, a1 p hBu⟩      -- 生欲界：此生離欲染而得（定品4）
  case «生初靜慮» => exact a6 p h               -- 生初靜慮（定品5）
  all_goals                                    -- 其餘各地都是二定以上，與前提相違
    exfalso
    apply hNot
    simp [«生二定以上», «生無色界», h]

/-- 【定品10】生在第二靜慮以上的不還，成就無漏初靜慮。
    依：定品3、智品1、智品2、智品3、賢聖品2。 -/
theorem «定品10成立» (W : «世界») (O : «本體公理» W)
    (a4 : «定品3» W) (a11 : «智品1» W) (a12 : «智品2» W) (a13 : «智品3» W)
    (k3 : «賢聖品2» W) : «定品10» W := by
  intro p ⟨hBu, hUp⟩
  rcases a4 p hUp with hYi | hSheng            -- 已離初靜慮染（定品3）：作異生時，或作聖者時
  · -- 作異生時已離初靜慮染：看入見道依何地
    have hYu : «已離欲染» W p := by            -- 有初靜慮染之分，必已離欲染（本體）
      cases hw : W.«欲染» p
      case «未離欲染» =>
        have h := (O.«適用_初靜慮染» p).2 (by simp [«已離欲染», hw])
        rw [hYi] at h
        cases h
      case «異生離欲染» => exact Or.inl hw
      case «聖者離欲染» => exact Or.inr hw
    cases hd : W.«見道依地» p
    case «依未至» =>
      rcases hYu with hYY | hSY
      · exact a12 p ⟨hBu, hd, hYY⟩             -- 先離欲染、依未至（智品2，待核）
      · exact absurd hYi (k3 p hSY)            -- 作聖者時才離欲染，不可能先已離初靜慮染（賢聖品2）
    case «依初靜慮» => exact a13 p (Or.inl hd)
    case «依靜慮中間» => exact a13 p (Or.inr (Or.inl hd))
    case «依第二靜慮» => exact a13 p (Or.inr (Or.inr (Or.inl hd)))
    case «依第三靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inl hd))))
    case «依第四靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inr hd))))
    case «—» =>                                 -- 聖者必有見道依地
      exact absurd ((O.«適用_見道依地» p).1 hd) (by simp [«不還是聖者» W p hBu])
  · exact a11 p hSheng                          -- 作聖者時離初靜慮染（智品1）

/-- 【定品11】生在第二靜慮以上的異生，不成就初靜慮。依：定品3、定品6、定品7、賢聖品5、定品1。 -/
theorem «定品11成立» (W : «世界») (a4 : «定品3» W) (a7 : «定品6» W) (a8 : «定品7» W)
    (a10 : «賢聖品5» W) (k1 : «定品1» W) : «定品11» W := by
  intro p ⟨hYi, hUp⟩ hCheng
  rcases (k1 p).1 hCheng with h | h | h
  · exact a8 p (a4 p hUp) h                    -- 味：已離初靜慮染，不成就（定品7）
  · exact a7 p hUp h                           -- 淨：易地而捨（定品6）
  · exact a10 p hYi h                          -- 無漏：異生不成就（賢聖品5）

/-- 【賢聖品6】預流、一來（及其向）不生上二界。依：賢聖品4、定品2。 -/
theorem «賢聖品6成立» (W : «世界») (a2 : «賢聖品4» W) (a3 : «定品2» W) : «賢聖品6» W :=
  fun p hPre hUp => a2 p hPre (a3 p hUp)

/-- 【智品5】不還都成就無漏初靜慮（若智品2成立）。依：賢聖品3、智品2、智品3、智品4。 -/
theorem «智品5成立» (W : «世界») (O : «本體公理» W)
    (a1 : «賢聖品3» W) (a12 : «智品2» W) (a13 : «智品3» W) (a14 : «智品4» W) :
    «智品5» W := by
  intro p hBu
  rcases a1 p hBu with hYY | hSY
  · cases hd : W.«見道依地» p
    case «依未至» => exact a12 p ⟨hBu, hd, hYY⟩
    case «依初靜慮» => exact a13 p (Or.inl hd)
    case «依靜慮中間» => exact a13 p (Or.inr (Or.inl hd))
    case «依第二靜慮» => exact a13 p (Or.inr (Or.inr (Or.inl hd)))
    case «依第三靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inl hd))))
    case «依第四靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inr hd))))
    case «—» => exact absurd ((O.«適用_見道依地» p).1 hd) (by simp [«不還是聖者» W p hBu])
  · exact a14 p hSY

/-- 【定品12】阿那含必然成就初靜慮。依：定品9、定品10、定品1。 -/
theorem «定品12成立» (W : «世界») (d1 : «定品9» W) (d2 : «定品10» W) (k1 : «定品1» W) :
    «定品12» W := by
  intro p hBu
  apply (k1 p).2
  cases h : W.«生地» p                         -- 就他生在哪一地分情況
  case «生欲界» =>                              -- 生欲界、初靜慮：淨（定品9）
    exact Or.inr (Or.inl (d1 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))
  case «生初靜慮» =>
    exact Or.inr (Or.inl (d1 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))
  all_goals                                     -- 生二定以上：無漏（定品10）
    exact Or.inr (Or.inr (d2 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))

/-- 把主證明拼起來：從九條假定、約定直接到目標。 -/
theorem «定品12由諸假定» (W : «世界») (O : «本體公理» W) (k1 : «定品1» W) (k3 : «賢聖品2» W)
    (a1 : «賢聖品3» W) (a4 : «定品3» W) (a5 : «定品4» W) (a6 : «定品5» W)
    (a11 : «智品1» W) (a12 : «智品2» W) (a13 : «智品3» W) : «定品12» W :=
  «定品12成立» W («定品9成立» W a1 a5 a6) («定品10成立» W O a4 a11 a12 a13 k3) k1

/-- 另一條證明：經由智品5，不分生地。 -/
theorem «定品12_經無漏» (W : «世界») (O : «本體公理» W) (k1 : «定品1» W)
    (a1 : «賢聖品3» W) (a12 : «智品2» W) (a13 : «智品3» W) (a14 : «智品4» W) :
    «定品12» W :=
  fun p hBu => (k1 p).2 (Or.inr (Or.inr («智品5成立» W O a1 a12 a13 a14 p hBu)))

end Kosa.Lib
